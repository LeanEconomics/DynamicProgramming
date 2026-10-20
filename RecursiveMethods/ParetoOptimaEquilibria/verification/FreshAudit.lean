import Mathlib
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Economies, Pareto optima and competitive equilibria

SLP §15.2, pp. 452–455. The commodity space is a real normed space `S`. There are finitely many
consumers `i : ι`, with consumption sets `X i ⊆ S` and utility functions `u i : S → ℝ` (only their
values on `X i` matter), and finitely many firms `j : κ`, with production sets `Y j ⊆ S`.

* `Feasible`: `xᵢ ∈ Xᵢ`, `yⱼ ∈ Yⱼ` and `Σ xᵢ − Σ yⱼ = 0` (p. 452).
* `ParetoOptimal`: feasible, and no feasible allocation makes every consumer at least as well off
  and some consumer strictly better off (p. 452).
* `CompetitiveEq`: with a price system `φ ∈ S*`, (E1) feasibility, (E2) each `xᵢ` maximises `uᵢ`
  on the budget set `{x ∈ Xᵢ : φ x ≤ φ xᵢ}`, (E3) each `yⱼ` maximises profit `φ` on `Yⱼ`
  (pp. 452–453).
* `LocalNonsatiation`: the hypothesis of Theorem 15.3.
* `Assumption15_1` … `Assumption15_5` (p. 455).
* `aggTech`: the aggregate technology `Y = Σⱼ Yⱼ`.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] {ι κ : Type*} [Fintype ι]
  [Fintype κ]

/-- An allocation `[(xᵢ), (yⱼ)]` is **feasible** (p. 452). -/
def Feasible (X : ι → Set S) (Y : κ → Set S) (x : ι → S) (y : κ → S) : Prop :=
  (∀ i, x i ∈ X i) ∧ (∀ j, y j ∈ Y j) ∧ ∑ i, x i - ∑ j, y j = 0

/-- A feasible allocation is **Pareto optimal** (p. 452). -/
def ParetoOptimal (X : ι → Set S) (u : ι → S → ℝ) (Y : κ → Set S) (x : ι → S) (y : κ → S) :
    Prop :=
  Feasible X Y x y ∧ ¬ ∃ x' y', Feasible X Y x' y' ∧ (∀ i, u i (x i) ≤ u i (x' i)) ∧
    ∃ i, u i (x i) < u i (x' i)

/-- `[(xᵢ), (yⱼ), φ]` is a **competitive equilibrium** (pp. 452–453): (E1)–(E3). -/
def CompetitiveEq (X : ι → Set S) (u : ι → S → ℝ) (Y : κ → Set S) (x : ι → S) (y : κ → S)
    (φ : StrongDual ℝ S) : Prop :=
  Feasible X Y x y ∧ (∀ i, ∀ z ∈ X i, φ z ≤ φ (x i) → u i z ≤ u i (x i)) ∧
    ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y j)

/-- **Local nonsatiation** (Theorem 15.3): every `x ∈ Xᵢ` is a limit of strictly preferred
points of `Xᵢ`. -/
def LocalNonsatiation (X : ι → Set S) (u : ι → S → ℝ) : Prop :=
  ∀ i, ∀ z ∈ X i, ∃ zs : ℕ → S, (∀ n, zs n ∈ X i) ∧ Tendsto zs atTop (𝓝 z) ∧
    ∀ n, u i z < u i (zs n)

/-- The aggregate technology `Y = Σⱼ Yⱼ` (p. 452). -/
def aggTech (Y : κ → Set S) : Set S :=
  {w | ∃ y : κ → S, (∀ j, y j ∈ Y j) ∧ w = ∑ j, y j}

/-- **Assumption 15.1**: each `Xᵢ` is convex. -/
def Assumption15_1 (X : ι → Set S) : Prop := ∀ i, Convex ℝ (X i)

/-- **Assumption 15.2**: if `uᵢ(x) > uᵢ(x′)` and `0 < θ < 1` then
`uᵢ(θx + (1 − θ)x′) > uᵢ(x′)`. -/
def Assumption15_2 (X : ι → Set S) (u : ι → S → ℝ) : Prop :=
  ∀ i, ∀ z ∈ X i, ∀ z' ∈ X i, u i z' < u i z → ∀ θ : ℝ, 0 < θ → θ < 1 →
    u i z' < u i (θ • z + (1 - θ) • z')

/-- **Assumption 15.3**: each `uᵢ` is continuous (on `Xᵢ`). -/
def Assumption15_3 (X : ι → Set S) (u : ι → S → ℝ) : Prop := ∀ i, ContinuousOn (u i) (X i)

/-- **Assumption 15.4**: the aggregate technology is convex. -/
def Assumption15_4 (Y : κ → Set S) : Prop := Convex ℝ (aggTech Y)

/-- **Assumption 15.5**: the aggregate technology has an interior point, or `S` is finite
dimensional. -/
def Assumption15_5 (S : Type*) [NormedAddCommGroup S] [NormedSpace ℝ S] {κ : Type*} [Fintype κ]
    (Y : κ → Set S) : Prop :=
  (interior (aggTech Y)).Nonempty ∨ FiniteDimensional ℝ S

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Second Welfare Theorem

SLP §15.2, pp. 454–458.

* Separation of disjoint convex sets, in the two cases of Assumption 15.5, proved here directly
  (the book's Theorem 15.2 is not used):
  * `exists_dual_nonneg_of_zero_notMem`: in a finite-dimensional space a nonempty convex set
    missing `0` lies in a half-space `{φ ≥ 0}`, `φ ≠ 0` (interior nonempty: Mathlib's
    `geometric_hahn_banach_of_nonempty_interior_point`; interior empty: the affine span is a
    proper affine subspace and a nonzero functional vanishing on its direction is constant on the
    set).
  * `exists_separating_of_finiteDimensional`, `exists_separating_of_interior`,
    `exists_separating_of_assumption15_5`: a nonzero `φ` with `φ(b) ≤ φ(a)` for `a ∈ A`, `b ∈ B`.
* `SupportsAllocation`: conditions (3) and (4) of Theorem 15.4 (a "quasi-equilibrium" price).
* **Theorem 15.4** (`theorem_15_4`, Second Welfare Theorem, p. 455): under Assumptions 15.1–15.5,
  a Pareto optimum with one nonsatiated consumer is supported by a nonzero continuous linear
  functional. `preferredSum` is the set `A = Åₕ + Σ_{i≠h} Aᵢ`; `convex_preferredSum`,
  `preferredSum_disjoint` and `le_of_weaklyPreferred` are steps 1–3 of the proof.
* **Remark** (`remark_cheaper_point`, p. 456): a supporting price with a cheaper point for every
  consumer is a competitive equilibrium price.
* `exists_better_of_localNonsatiation` and `welfare_theorems_corrected`: the corrected form of the
  p. 458 claim that "the CE and PO allocations coincide" (see `WelfareExamples` for the
  counterexamples to the book's version).

**Corrections** (to the proof of Theorem 15.4; see also `Welfare`).
* Step 1: the convexity of `Aᵢ`, `Åᵢ` uses Assumptions 15.1–15.3, not 15.2 alone
  (`convex_weaklyPreferred`, `assumption15_2_convex_counterexample`).
* Step 3: the extension from `Åₕ + Σ_{i≠h} Aᵢ` to `Σᵢ Aᵢ` uses `Aₕ ⊆ cl Åₕ` (15.1, 15.2 and
  `x̂ₕ`) and continuity of `φ`, not continuity of `uₕ` (`le_of_weaklyPreferred`,
  `continuity_closure_counterexample`).
* Step 4: the book does not state that the separating constant is `c = φ(Σᵢ xᵢ⁰) = φ(Σⱼ yⱼ⁰)`,
  which is what turns the separation into (3) and (4). Here the separation is stated without a
  constant and (3), (4) are derived by comparing with `Σᵢ xᵢ⁰ = Σⱼ yⱼ⁰`, which lies in both
  `Σᵢ Aᵢ` and `Y`.
* Theorem 15.2 needs `A ≠ ∅` (and `B ≠ ∅` in finite dimensions); in Theorem 15.4 both sets are
  nonempty (`preferredSum_nonempty`).
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Set Pointwise

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] {ι κ : Type*} [Fintype ι]
  [Fintype κ]

/-! ### Separation -/

/-- In a finite-dimensional normed space, a nonempty convex set `C` with `0 ∉ C` lies in a closed
half-space `{φ ≥ 0}` of a nonzero continuous linear functional `φ`. -/
theorem exists_dual_nonneg_of_zero_notMem [FiniteDimensional ℝ S] {C : Set S}
    (hC : Convex ℝ C) (hne : C.Nonempty) (h0 : (0 : S) ∉ C) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∀ c ∈ C, 0 ≤ φ c := by
  by_cases hint : (interior C).Nonempty
  · obtain ⟨f, hf0, hf⟩ := geometric_hahn_banach_of_nonempty_interior_point hC
      (fun h => h0 (interior_subset h)) hint
    refine ⟨-f, neg_ne_zero.2 hf0, fun c hc => ?_⟩
    have := hf c hc
    simp only [map_zero] at this
    simp only [neg_apply]
    linarith
  · have hspan : affineSpan ℝ C ≠ ⊤ := fun h =>
      hint (hC.interior_nonempty_iff_affineSpan_eq_top.2 h)
    have hdir : (affineSpan ℝ C).direction ≠ ⊤ := fun h =>
      hspan ((AffineSubspace.direction_eq_top_iff_of_nonempty
        ((affineSpan_nonempty (k := ℝ)).2 hne)).1 h)
    obtain ⟨g, hg0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hdir)
    obtain ⟨c0, hc0⟩ := hne
    have hconst : ∀ c ∈ C, g c = g c0 := fun c hc => by
      have hmem : c -ᵥ c0 ∈ (affineSpan ℝ C).direction :=
        AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hc) (mem_affineSpan ℝ hc0)
      have := hle hmem
      rw [LinearMap.mem_ker, vsub_eq_sub, map_sub] at this
      linarith
    set f : StrongDual ℝ S := LinearMap.toContinuousLinearMap g with hf
    have hfg : ∀ v, f v = g v := fun v => rfl
    have hf0 : f ≠ 0 := fun h => hg0 (LinearMap.ext fun v => by
      rw [← hfg, h]
      rfl)
    rcases le_total 0 (g c0) with hs | hs
    · exact ⟨f, hf0, fun c hc => by rw [hfg, hconst c hc]; exact hs⟩
    · refine ⟨-f, neg_ne_zero.2 hf0, fun c hc => ?_⟩
      rw [neg_apply, hfg, hconst c hc]
      linarith

/-- **Separation in finite dimensions**: disjoint nonempty convex sets `A`, `B` of a
finite-dimensional normed space are separated by a nonzero continuous linear functional,
`φ(b) ≤ φ(a)` for `a ∈ A`, `b ∈ B`. -/
theorem exists_separating_of_finiteDimensional [FiniteDimensional ℝ S] {A B : Set S}
    (hA : Convex ℝ A) (hB : Convex ℝ B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hdisj : Disjoint A B) : ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ B, φ b ≤ φ a := by
  obtain ⟨φ, hφ0, hφ⟩ := exists_dual_nonneg_of_zero_notMem (hA.sub hB) (hAne.sub hBne)
    hdisj.zero_notMem_sub_set
  refine ⟨φ, hφ0, fun a ha b hb => ?_⟩
  have := hφ (a - b) (sub_mem_sub ha hb)
  rw [map_sub] at this
  linarith

/-- **Separation with an interior point** (Mathlib's geometric Hahn–Banach): if `B` is convex with
nonempty interior, `A` is convex and nonempty, and `A ∩ B = ∅`, then a nonzero continuous linear
functional has `φ(b) ≤ φ(a)` for `a ∈ A`, `b ∈ B`. -/
theorem exists_separating_of_interior {A B : Set S} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hAne : A.Nonempty) (hBint : (interior B).Nonempty) (hdisj : Disjoint A B) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ B, φ b ≤ φ a := by
  obtain ⟨f, c, hf0, hfB, hfA⟩ := geometric_hahn_banach_of_nonempty_interior hB hA
    (hdisj.symm.mono_left interior_subset) hBint hAne
  exact ⟨f, hf0, fun a ha b hb => (hfB b hb).trans (hfA a ha)⟩

/-- Separation under the dichotomy of Assumption 15.5: `B` has an interior point or `S` is finite
dimensional. -/
theorem exists_separating_of_assumption15_5 {A B : Set S} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hdisj : Disjoint A B)
    (h5 : (interior B).Nonempty ∨ FiniteDimensional ℝ S) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ B, φ b ≤ φ a := by
  rcases h5 with h | h
  · exact exists_separating_of_interior hA hB hAne h hdisj
  · have := h
    exact exists_separating_of_finiteDimensional hA hB hAne hBne hdisj

/-! ### Theorem 15.4 -/

/-- Conditions (3) and (4) of Theorem 15.4: `φ` supports the allocation, i.e. each `xᵢ⁰` minimises
cost over the weakly preferred set `Aᵢ` and each `yⱼ⁰` maximises profit over `Yⱼ`. -/
def SupportsAllocation (X : ι → Set S) (u : ι → S → ℝ) (Y : κ → Set S) (x : ι → S) (y : κ → S)
    (φ : StrongDual ℝ S) : Prop :=
  (∀ i, ∀ z ∈ X i, u i (x i) ≤ u i z → φ (x i) ≤ φ z) ∧ ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y j)

/-- The set `A = Åₕ + Σ_{i≠h} Aᵢ` of the proof of Theorem 15.4: sums `Σᵢ zᵢ` with every `zᵢ` in
the weakly preferred set `Aᵢ` and `zₕ` in the strictly preferred set `Åₕ`. -/
def preferredSum (X : ι → Set S) (u : ι → S → ℝ) (x : ι → S) (h : ι) : Set S :=
  {w | ∃ z : ι → S, (∀ i, z i ∈ X i ∧ u i (x i) ≤ u i (z i)) ∧ u h (x h) < u h (z h) ∧
    w = ∑ i, z i}

/-- Step 1–2 of the proof of Theorem 15.4: `A` is convex (Assumptions 15.1–15.3). -/
theorem convex_preferredSum {X : ι → Set S} {u : ι → S → ℝ} (h1 : Assumption15_1 X)
    (h2 : Assumption15_2 X u) (h3 : Assumption15_3 X u) (x : ι → S) (h : ι) :
    Convex ℝ (preferredSum X u x h) := by
  rintro _ ⟨z, hz, hzh, rfl⟩ _ ⟨z', hz', hzh', rfl⟩ a b ha hb hab
  refine ⟨fun i => a • z i + b • z' i, fun i => ?_, ?_, ?_⟩
  · exact convex_weaklyPreferred (h1 i) (h2 i) (h3 i) _ (hz i) (hz' i) ha hb hab
  · exact (convex_strictlyPreferred (h1 h) (h2 h) (h3 h) _ ⟨(hz h).1, hzh⟩
      ⟨(hz' h).1, hzh'⟩ ha hb hab).2
  · rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]

omit [NormedSpace ℝ S] in
/-- `A` is nonempty when consumer `h` has a strictly better point `x̂ₕ`. -/
theorem preferredSum_nonempty {X : ι → Set S} {u : ι → S → ℝ} {x : ι → S}
    (hx : ∀ i, x i ∈ X i) {h : ι} {xhat : S} (hxhat : xhat ∈ X h)
    (hsat : u h (x h) < u h xhat) : (preferredSum X u x h).Nonempty := by
  classical
  refine ⟨_, Function.update x h xhat, fun i => ?_, by simpa using hsat, rfl⟩
  rcases eq_or_ne i h with rfl | hi
  · simp only [Function.update_self]
    exact ⟨hxhat, hsat.le⟩
  · simp only [Function.update_of_ne hi]
    exact ⟨hx i, le_rfl⟩

omit [NormedSpace ℝ S] in
/-- Step 2 of the proof of Theorem 15.4: at a Pareto optimum, `A ∩ Y = ∅`. -/
theorem preferredSum_disjoint {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S}
    {y : κ → S} (hPO : ParetoOptimal X u Y x y) (h : ι) :
    Disjoint (preferredSum X u x h) (aggTech Y) := by
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, hzh, rfl⟩ ⟨y', hy', hsum⟩
  exact hPO.2 ⟨z, y', ⟨fun i => (hz i).1, hy', sub_eq_zero.2 hsum⟩, fun i => (hz i).2, h, hzh⟩

/-- Step 3 of the proof of Theorem 15.4, corrected: if `φ(b) ≤ φ(a)` for `a ∈ A`, `b ∈ Y`, then
also `φ(b) ≤ φ(Σᵢ zᵢ)` for every `(zᵢ)` with `zᵢ ∈ Aᵢ` for all `i`. The reason is `Aₕ ⊆ cl Åₕ`
(`weaklyPreferred_subset_closure`) and continuity of `φ`. -/
theorem le_of_weaklyPreferred {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) {h : ι} {xhat : S} (hxhat : xhat ∈ X h)
    (hsat : u h (x h) < u h xhat) {φ : StrongDual ℝ S}
    (hsep : ∀ a ∈ preferredSum X u x h, ∀ b ∈ aggTech Y, φ b ≤ φ a) (z : ι → S)
    (hz : ∀ i, z i ∈ X i ∧ u i (x i) ≤ u i (z i)) {b : S} (hb : b ∈ aggTech Y) :
    φ b ≤ φ (∑ i, z i) := by
  classical
  set R := ∑ i ∈ Finset.univ \ {h}, z i with hR
  have hstrict : {v | v ∈ X h ∧ u h (x h) < u h v} ⊆ {v | φ b ≤ φ (v + R)} := by
    rintro v ⟨hv, hvlt⟩
    have hmem : ∑ i, Function.update z h v i ∈ preferredSum X u x h := by
      refine ⟨Function.update z h v, fun i => ?_, by simpa using hvlt, rfl⟩
      rcases eq_or_ne i h with rfl | hi
      · simp only [Function.update_self]
        exact ⟨hv, hvlt.le⟩
      · simp only [Function.update_of_ne hi]
        exact hz i
    have := hsep _ hmem b hb
    rwa [Finset.sum_update_of_mem (Finset.mem_univ h)] at this
  have hclosed : IsClosed {v | φ b ≤ φ (v + R)} :=
    isClosed_le continuous_const (φ.continuous.comp (continuous_id.add continuous_const))
  have hzh : z h ∈ {v | φ b ≤ φ (v + R)} :=
    closure_minimal hstrict hclosed
      (weaklyPreferred_subset_closure (h1 h) (h2 h) hxhat hsat (hz h))
  rwa [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ h)]

/-- **Theorem 15.4** (Second Welfare Theorem, p. 455). Under Assumptions 15.1–15.5, if
`[(xᵢ⁰), (yⱼ⁰)]` is Pareto optimal and some consumer `h` has `x̂ₕ ∈ Xₕ` with
`uₕ(x̂ₕ) > uₕ(xₕ⁰)`, then a nonzero continuous linear functional `φ` satisfies (3) and (4). -/
theorem theorem_15_4 {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S} {y : κ → S}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) (h3 : Assumption15_3 X u)
    (h4 : Assumption15_4 Y) (h5 : Assumption15_5 S Y) (hPO : ParetoOptimal X u Y x y)
    {h : ι} {xhat : S} (hxhat : xhat ∈ X h) (hsat : u h (x h) < u h xhat) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ SupportsAllocation X u Y x y φ := by
  classical
  obtain ⟨hxX, hyY, hxy⟩ := hPO.1
  obtain ⟨φ, hφ0, hsep⟩ := exists_separating_of_assumption15_5
    (convex_preferredSum h1 h2 h3 x h) h4 (preferredSum_nonempty hxX hxhat hsat)
    ⟨_, y, hyY, rfl⟩ (preferredSum_disjoint hPO h) h5
  have hext := le_of_weaklyPreferred h1 h2 hxhat hsat hsep
  have hxy' : ∑ i, x i = ∑ j, y j := sub_eq_zero.mp hxy
  refine ⟨φ, hφ0, fun i z hz hle => ?_, fun j w hw => ?_⟩
  · -- (3): compare `Σⱼ yⱼ⁰ = Σᵢ xᵢ⁰ ∈ Y` with `z + Σ_{i' ≠ i} xᵢ'⁰ ∈ Σᵢ Aᵢ`
    have key := hext (Function.update x i z) (fun i' => by
      rcases eq_or_ne i' i with rfl | hi
      · simp only [Function.update_self]
        exact ⟨hz, hle⟩
      · simp only [Function.update_of_ne hi]
        exact ⟨hxX i', le_rfl⟩) (b := ∑ j, y j) ⟨y, hyY, rfl⟩
    rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← hxy',
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i), map_add,
      map_add] at key
    linarith
  · -- (4): compare `w + Σ_{j' ≠ j} yⱼ'⁰ ∈ Y` with `Σᵢ xᵢ⁰ ∈ Σᵢ Aᵢ`
    have key := hext x (fun i' => ⟨hxX i', le_rfl⟩)
      (b := ∑ j', Function.update y j w j') ⟨Function.update y j w, fun j' => by
        rcases eq_or_ne j' j with rfl | hj
        · simp only [Function.update_self]
          exact hw
        · simp only [Function.update_of_ne hj]
          exact hyY j', rfl⟩
    rw [Finset.sum_update_of_mem (Finset.mem_univ j), hxy',
      Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j), map_add,
      map_add] at key
    linarith

/-! ### The Remark on p. 456 -/

/-- **Remark** (cheaper point ⇒ competitive equilibrium, p. 456). Under Assumptions 15.1 and 15.3,
if `[(xᵢ⁰), (yⱼ⁰)]` is feasible, `φ` satisfies (3) and (4), and every consumer has a cheaper point
`xᵢ′ ∈ Xᵢ`, `φ(xᵢ′) < φ(xᵢ⁰)`, then `[(xᵢ⁰), (yⱼ⁰), φ]` is a competitive equilibrium. -/
theorem remark_cheaper_point {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S}
    {y : κ → S} {φ : StrongDual ℝ S} (h1 : Assumption15_1 X) (h3 : Assumption15_3 X u)
    (hF : Feasible X Y x y) (hφ : SupportsAllocation X u Y x y φ)
    (hcheap : ∀ i, ∃ z ∈ X i, φ z < φ (x i)) : CompetitiveEq X u Y x y φ := by
  refine ⟨hF, fun i z hz hzle => ?_, hφ.2⟩
  obtain ⟨x', hx', hlt⟩ := hcheap i
  set p : ℝ → S := fun θ => θ • x' + (1 - θ) • z with hp
  have hpc : Continuous p := by fun_prop
  have hp0 : p 0 = z := by simp [hp]
  have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), p θ ∈ X i ∧ u i (p θ) < u i (x i) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
    have hpX : p θ ∈ X i := h1 i hx' hz hθ.1.le (by linarith [hθ.2]) (by ring)
    refine ⟨hpX, ?_⟩
    by_contra hge
    push Not at hge
    have hcost := hφ.1 i (p θ) hpX hge
    simp only [hp, map_add, map_smul, smul_eq_mul] at hcost
    nlinarith [hθ.1, hθ.2]
  have hlim : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝[X i] z) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hev.mono fun θ hθ => hθ.1⟩
    rw [← hp0]
    exact (hpc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ((h3 i z hz).tendsto.comp hlim) (hev.mono fun θ hθ => hθ.2.le)

/-! ### The corrected form of the p. 458 claim -/

omit [NormedSpace ℝ S] [Fintype ι] in
/-- Under local nonsatiation every consumer has a strictly better point than any `xᵢ ∈ Xᵢ`; this
supplies the hypothesis `x̂ₕ` of Theorem 15.4. -/
theorem exists_better_of_localNonsatiation {X : ι → Set S} {u : ι → S → ℝ}
    (hLNS : LocalNonsatiation X u) {x : ι → S} (hx : ∀ i, x i ∈ X i) (i : ι) :
    ∃ xhat ∈ X i, u i (x i) < u i xhat := by
  obtain ⟨zs, hzsX, -, hzsu⟩ := hLNS i (x i) (hx i)
  exact ⟨zs 0, hzsX 0, hzsu 0⟩

/-- **The welfare theorems, correctly combined** (the NOTE to p. 458). With local nonsatiation and
Assumptions 15.1–15.5, and at least one consumer:
(a) every competitive equilibrium allocation is Pareto optimal (Theorem 15.3);
(b) every Pareto optimum is supported by a nonzero continuous linear functional satisfying (3),
(4) (Theorem 15.4);
(c) a Pareto optimum is a competitive equilibrium allocation if some nonzero supporting
functional leaves every consumer a cheaper point (Remark).
The book's "the two sets coincide exactly" is false (`WelfareExamples`). -/
theorem welfare_theorems_corrected [Nonempty ι] {X : ι → Set S} {u : ι → S → ℝ}
    {Y : κ → Set S} (hLNS : LocalNonsatiation X u) (h1 : Assumption15_1 X)
    (h2 : Assumption15_2 X u) (h3 : Assumption15_3 X u) (h4 : Assumption15_4 Y)
    (h5 : Assumption15_5 S Y) (x : ι → S) (y : κ → S) :
    ((∃ φ, CompetitiveEq X u Y x y φ) → ParetoOptimal X u Y x y) ∧
    (ParetoOptimal X u Y x y → ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ SupportsAllocation X u Y x y φ) ∧
    (ParetoOptimal X u Y x y → ∀ φ : StrongDual ℝ S, SupportsAllocation X u Y x y φ →
      (∀ i, ∃ z ∈ X i, φ z < φ (x i)) → CompetitiveEq X u Y x y φ) := by
  refine ⟨fun ⟨φ, hφ⟩ => theorem_15_3 hLNS hφ, fun hPO => ?_,
    fun hPO φ hφ hcheap => remark_cheaper_point h1 h3 hPO.1 hφ hcheap⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨xhat, hxhat, hsat⟩ := exists_better_of_localNonsatiation hLNS hPO.1.1 i
  exact theorem_15_4 h1 h2 h3 h4 h5 hPO hxhat hsat

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Issues in the choice of a commodity space

SLP §15.3, pp. 458–462. Sequences are indexed by `t : ℕ`; in the book's ℓ_∞ example the periods
are `t = 1, 2, …`, so the book's period `t + 1` is index `t` here.

* **Exercise 15.7** (p. 460): (a) `ex_15_7a`: for `1 ≤ p < ∞` the positive orthant
  `lpPosOrthant p` of `ℓ_p` has empty interior; (b) `ex_15_7b`: the positive orthant of `ℓ_∞`
  has nonempty interior (it contains the ball of radius `1/2` about `(1, 1, …)`).
* The example on pp. 460–461: `S = ℓ_∞`, one consumer with `X = ℓ_∞⁺` and `u(x) = inf_t x_t`
  (`ex158X`, `ex158U`), one firm with `Y = {y : 0 ≤ y_t ≤ 1 + 1/t}` (`ex158Y`).
  * **Exercise 15.8** (`ex_15_8`): the economy satisfies Assumptions 15.1–15.5 (15.3 via
    `abs_ex158U_sub_le`, `|u x − u x′| ≤ ‖x − x′‖_∞`; 15.5 via `half_mem_interior_ex158Y`).
  * `ex158_paretoOptimal`: `x⁰ = y⁰ = (1 + 1/t)_t` is Pareto optimal; `ex158_exists_price`:
    Theorem 15.4 gives a nonzero supporting `φ ∈ ℓ_∞*`.
  * `ex158_price_vanishes_single`: every `φ` satisfying (2) and (3) vanishes on every unit
    sequence `e_t` (hence on all finitely supported sequences): "all its weight at infinity".
  * `ex158_no_inner_product`: no nonzero such `φ` has the form `φ(x) = Σ_t p_t x_t`
    (§15.3 (4)).
* **Exercise 15.9** (`ex_15_9`, p. 462): with the weighted norm (5),
  `‖x‖ = Σ_t β^t |x_t|`, the utility `u(x) = inf_t x_t` is not continuous at `(1, 1, …)` on the
  positive orthant (`weightedDist` is the distance of the norm (5)).
* NOTE to p. 462: `weighted_orthant_no_interior` — in the norm (5) no point of the positive
  orthant is interior; so no subset of it (in particular not `Y`) has an interior point
  (`weighted_no_interior_of_subset_orthant`). This is what the book needs; Exercise 15.6 itself
  is about the box `{|x_t| ≤ 1}`.
* NOTE to p. 462 (indexing): `hasSum_state_probabilities` — the probabilities `β^t(1 − β)` sum to
  `1` over `t = 0, 1, …`, so the stochastic re-reading of the example (indexed `t = 1, 2, …`) must
  use `β^{t−1}(1 − β)`.

**Corrections.** None to the exercises (the manual's solutions are correct). The p. 462 sentence
"by Exercise 15.6 the positive orthant has no interior point" cites the wrong result; the claim
is true and is proved directly here (`weighted_orthant_no_interior`).
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Set
open scoped ENNReal

/-- With a single firm the aggregate technology is that firm's production set. -/
theorem aggTech_of_unit {S : Type*} [NormedAddCommGroup S] (Y : Unit → Set S) :
    aggTech Y = Y () := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy ()
  · intro hw
    exact ⟨fun _ => w, fun _ => hw, by simp⟩

/-! ### Exercise 15.7 -/

/-- The positive orthant `ℓ_p⁺ = {x ∈ ℓ_p : x_t ≥ 0 for all t}`. -/
def lpPosOrthant (p : ℝ≥0∞) : Set (lp (fun _ : ℕ => ℝ) p) := {x | ∀ t, 0 ≤ x t}

/-- **Exercise 15.7(a)**: for `1 ≤ p < ∞` the positive orthant of `ℓ_p` has no interior point.
Given `x` and `ε > 0`, some coordinate has `|x_N| < ε/2` (as `x_t → 0`); lowering it to `−ε/2`
moves less than `ε` and leaves the orthant. -/
theorem ex_15_7a {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) : interior (lpPosOrthant p) = ∅ := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos (Fact.out : 1 ≤ p)
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0.ne' hp
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx)
  have hsum : Summable fun t => ‖x t‖ ^ p.toReal := (memℓp_gen_iff hpr).1 x.prop
  have hev : ∀ᶠ t in atTop, ‖x t‖ ^ p.toReal < (ε / 2) ^ p.toReal :=
    Filter.Tendsto.eventually_lt_const (Real.rpow_pos_of_pos (by linarith) _)
      hsum.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := hev.exists
  have hxN : |x N| < ε / 2 := by
    rw [← Real.norm_eq_abs]
    exact (Real.rpow_lt_rpow_iff (norm_nonneg _) (by linarith) hpr).1 hN
  rw [abs_lt] at hxN
  set c := x N + ε / 2 with hc
  set z := x - lp.single p N c with hz
  have hzball : z ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, hz, sub_sub_cancel_left, norm_neg, lp.norm_single hp0,
      Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  have := hball hzball N
  simp only [hz, lp.coeFn_sub, Pi.sub_apply, lp.single_apply, Pi.single_eq_same] at this
  linarith

/-- **Exercise 15.7(b)**: the positive orthant of `ℓ_∞` has an interior point, `(1, 1, …)`: the
ball of radius `1/2` about it lies in the orthant. -/
theorem ex_15_7b : (1 : lp (fun _ : ℕ => ℝ) ∞) ∈ interior (lpPosOrthant ∞) := by
  refine mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨1 / 2, by norm_num, fun y hy t => ?_⟩)
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have h := (lp.norm_apply_le_norm ENNReal.top_ne_zero (y - 1) t).trans_lt hy
  rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_one, Pi.one_apply, Real.norm_eq_abs,
    abs_lt] at h
  linarith [h.1]

/-! ### The ℓ_∞ example of pp. 460–461 and Exercise 15.8 -/

/-- Consumption set of the p. 460 example: `X = ℓ_∞⁺`. -/
def ex158X : Unit → Set (lp (fun _ : ℕ => ℝ) ∞) := fun _ => lpPosOrthant ∞

/-- Production set of the p. 460 example: `Y = {y : 0 ≤ y_t ≤ 1 + 1/t}` (book period `t + 1` is
index `t`). -/
def ex158Y : Unit → Set (lp (fun _ : ℕ => ℝ) ∞) :=
  fun _ => {y | ∀ t, 0 ≤ y t ∧ y t ≤ 1 + 1 / ((t : ℝ) + 1)}

/-- Utility of the p. 460 example, §15.3 (1): `u(x) = inf_t x_t`. -/
noncomputable def ex158U : Unit → lp (fun _ : ℕ => ℝ) ∞ → ℝ := fun _ x => ⨅ t, x t

/-- The coordinates of a bounded sequence are bounded below. -/
theorem bddBelow_range_lpInfty (x : lp (fun _ : ℕ => ℝ) ∞) : BddBelow (range fun t => x t) := by
  refine ⟨-‖x‖, ?_⟩
  rintro _ ⟨t, rfl⟩
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero x t
  rw [Real.norm_eq_abs] at this
  linarith [neg_abs_le (x t)]

/-- `inf_t x_t ≤ x_s`. -/
theorem ex158U_le (x : lp (fun _ : ℕ => ℝ) ∞) (s : ℕ) : ex158U () x ≤ x s :=
  ciInf_le (bddBelow_range_lpInfty x) s

/-- A lower bound for every coordinate is a lower bound for `inf_t x_t`. -/
theorem le_ex158U {x : lp (fun _ : ℕ => ℝ) ∞} {c : ℝ} (h : ∀ t, c ≤ x t) : c ≤ ex158U () x :=
  le_ciInf h

/-- If `x_t ≤ 1 + 1/(t + 1)` for all `t` then `inf_t x_t ≤ 1`. -/
theorem ex158U_le_one {x : lp (fun _ : ℕ => ℝ) ∞} (h : ∀ t, x t ≤ 1 + 1 / ((t : ℝ) + 1)) :
    ex158U () x ≤ 1 := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  linarith [ex158U_le x n, h n]

/-- `|inf x − inf x′| ≤ ‖x − x′‖_∞` (the one-line fact behind the manual's Assumption 15.3
argument). -/
theorem abs_ex158U_sub_le (x x' : lp (fun _ : ℕ => ℝ) ∞) :
    |ex158U () x - ex158U () x'| ≤ ‖x - x'‖ := by
  have hcoord : ∀ t, |x t - x' t| ≤ ‖x - x'‖ := fun t => by
    have := lp.norm_apply_le_norm ENNReal.top_ne_zero (x - x') t
    rwa [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] at this
  rw [abs_le]
  constructor
  · have : ex158U () x' - ‖x - x'‖ ≤ ex158U () x := le_ex158U fun t => by
      linarith [ex158U_le x' t, (abs_le.1 (hcoord t)).1]
    linarith
  · have : ex158U () x - ‖x - x'‖ ≤ ex158U () x' := le_ex158U fun t => by
      linarith [ex158U_le x t, (abs_le.1 (hcoord t)).2]
    linarith

/-- The constant sequence `(1/2, 1/2, …)` is an interior point of `Y` (radius `1/2`). -/
theorem half_mem_interior_ex158Y :
    ((1 / 2 : ℝ) • (1 : lp (fun _ : ℕ => ℝ) ∞)) ∈ interior (ex158Y ()) := by
  refine mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨1 / 2, by norm_num, fun w hw t => ?_⟩)
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h := (lp.norm_apply_le_norm ENNReal.top_ne_zero (w - (1 / 2 : ℝ) • 1) t).trans_lt hw
  rw [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, lp.infty_coeFn_one,
    Pi.one_apply, smul_eq_mul, mul_one, Real.norm_eq_abs, abs_lt] at h
  have : (0 : ℝ) ≤ 1 / ((t : ℝ) + 1) := by positivity
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **Exercise 15.8** (p. 460): the economy `S = ℓ_∞`, `X = ℓ_∞⁺`, `u(x) = inf_t x_t`,
`Y = {0 ≤ y_t ≤ 1 + 1/t}` satisfies Assumptions 15.1–15.5. -/
theorem ex_15_8 :
    Assumption15_1 ex158X ∧ Assumption15_2 ex158X ex158U ∧ Assumption15_3 ex158X ex158U ∧
    Assumption15_4 ex158Y ∧ Assumption15_5 (lp (fun _ : ℕ => ℝ) ∞) ex158Y := by
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, ?_, ?_⟩
  · intro x hx x' hx' a b ha hb _ t
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx t
    have := hx' t
    positivity
  · intro z _ z' _ hlt θ hθ0 hθ1
    have hlow : θ * ex158U () z + (1 - θ) * ex158U () z' ≤ ex158U () (θ • z + (1 - θ) • z') :=
      le_ex158U fun t => by
        simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h1 := mul_le_mul_of_nonneg_left (ex158U_le z t) hθ0.le
        have h2 := mul_le_mul_of_nonneg_left (ex158U_le z' t) (sub_nonneg.2 hθ1.le)
        linarith
    nlinarith
  · refine Continuous.continuousOn ?_
    refine (LipschitzWith.of_dist_le_mul fun x x' => ?_).continuous (K := 1)
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
    exact abs_ex158U_sub_le x x'
  · rw [Assumption15_4, aggTech_of_unit]
    intro y hy y' hy' a b ha hb hab t
    simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨h1, h2⟩ := hy t
    obtain ⟨h3, h4⟩ := hy' t
    constructor
    · positivity
    · have := mul_le_mul_of_nonneg_left h2 ha
      have := mul_le_mul_of_nonneg_left h4 hb
      nlinarith
  · left
    rw [aggTech_of_unit]
    exact ⟨_, half_mem_interior_ex158Y⟩

/-- The Pareto-optimal allocation of the example: `x⁰ = y⁰ = (1 + 1/t)_t`. -/
noncomputable def ex158x0 : lp (fun _ : ℕ => ℝ) ∞ :=
  ⟨fun t => 1 + 1 / ((t : ℝ) + 1), memℓp_infty_iff.2 ⟨2, by
    rintro _ ⟨t, rfl⟩
    have h0 : (0 : ℝ) ≤ 1 / ((t : ℝ) + 1) := by positivity
    have h1 : 1 / ((t : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    linarith⟩⟩

/-- Coordinates of `x⁰`. -/
theorem ex158x0_apply (t : ℕ) : ex158x0 t = 1 + 1 / ((t : ℝ) + 1) := rfl

/-- `u(x⁰) = 1`. -/
theorem ex158U_x0 : ex158U () ex158x0 = 1 := by
  refine le_antisymm (ex158U_le_one fun t => le_rfl) (le_ex158U fun t => ?_)
  rw [ex158x0_apply]
  have : (0 : ℝ) ≤ 1 / ((t : ℝ) + 1) := by positivity
  linarith

/-- The allocation `x⁰ = y⁰ = (1 + 1/t)_t` of the example is Pareto optimal (any feasible `x`
has `x_t ≤ 1 + 1/t`, so `u(x) ≤ 1 = u(x⁰)`). -/
theorem ex158_paretoOptimal :
    ParetoOptimal ex158X ex158U ex158Y (fun _ => ex158x0) (fun _ => ex158x0) := by
  have hpos : ∀ t, 0 ≤ ex158x0 t := fun t => by
    rw [ex158x0_apply]
    positivity
  refine ⟨⟨fun _ => hpos, fun _ t => ⟨hpos t, le_rfl⟩, by simp⟩, ?_⟩
  rintro ⟨x', y', ⟨-, hy', hsum⟩, -, i, hi⟩
  have hxy : x' () = y' () := by simpa [sub_eq_zero] using hsum
  have hle : ex158U () (x' ()) ≤ 1 := ex158U_le_one fun t => by
    rw [hxy]
    exact (hy' () t).2
  cases i
  rw [ex158U_x0] at hi
  linarith

/-- Consumer nonsatiation at `x⁰`: `x̂ = (2, 2, …)` has `u(x̂) = 2 > 1 = u(x⁰)`. -/
theorem ex158_nonsatiated :
    (2 : ℝ) • (1 : lp (fun _ : ℕ => ℝ) ∞) ∈ ex158X () ∧
    ex158U () ex158x0 < ex158U () ((2 : ℝ) • (1 : lp (fun _ : ℕ => ℝ) ∞)) := by
  have hc : ∀ t, ((2 : ℝ) • (1 : lp (fun _ : ℕ => ℝ) ∞)) t = 2 := fun t => by
    rw [lp.coeFn_smul, Pi.smul_apply, lp.infty_coeFn_one, Pi.one_apply, smul_eq_mul, mul_one]
  refine ⟨fun t => by rw [hc]; norm_num, ?_⟩
  rw [ex158U_x0]
  have : (2 : ℝ) ≤ ex158U () ((2 : ℝ) • 1) := le_ex158U fun t => (hc t).ge
  linarith

/-- By Theorem 15.4 the example has a nonzero supporting price `φ ∈ ℓ_∞*` satisfying §15.3 (2)
and (3). -/
theorem ex158_exists_price : ∃ φ : StrongDual ℝ (lp (fun _ : ℕ => ℝ) ∞), φ ≠ 0 ∧
    SupportsAllocation ex158X ex158U ex158Y (fun _ => ex158x0) (fun _ => ex158x0) φ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ex_15_8
  exact theorem_15_4 h1 h2 h3 h4 h5 ex158_paretoOptimal ex158_nonsatiated.1 ex158_nonsatiated.2

/-- The unit sequence `e_t ∈ ℓ_∞` (`1` in position `t`, `0` elsewhere). -/
noncomputable def ex158e (t : ℕ) : lp (fun _ : ℕ => ℝ) ∞ := lp.single ∞ t 1

/-- Coordinates of `e_t`. -/
theorem ex158e_apply (t s : ℕ) : ex158e t s = if s = t then 1 else 0 := by
  rcases eq_or_ne s t with rfl | hs
  · simp [ex158e]
  · simp [ex158e, hs]

/-- Coordinates of `x⁰ − c e_t`. -/
theorem ex158x0_sub_single_apply (c : ℝ) (t s : ℕ) :
    (ex158x0 - c • ex158e t) s = if s = t then ex158x0 t - c else ex158x0 s := by
  rw [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, ex158e_apply, smul_eq_mul]
  split_ifs with hs
  · rw [hs, mul_one]
  · rw [mul_zero, sub_zero]

/-- **All weight at infinity** (p. 461): any `φ` satisfying §15.3 (2) and (3) vanishes on every
unit sequence `e_t`. From (3) with `y⁰ − y⁰_t e_t ∈ Y`, `φ(e_t) ≥ 0`; from (2) with
`x⁰ − e_t/(t + 1)`, which has utility `1 = u(x⁰)`, `φ(e_t) ≤ 0`. -/
theorem ex158_price_vanishes_single {φ : StrongDual ℝ (lp (fun _ : ℕ => ℝ) ∞)}
    (hφ : SupportsAllocation ex158X ex158U ex158Y (fun _ => ex158x0) (fun _ => ex158x0) φ)
    (t : ℕ) : φ (ex158e t) = 0 := by
  have ht0 : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
  -- the firm: profit maximisation
  have hY : ex158x0 - ex158x0 t • ex158e t ∈ ex158Y () := fun s => by
    rw [ex158x0_sub_single_apply]
    split_ifs with hs
    · simp only [sub_self, le_refl, true_and]
      positivity
    · exact ⟨by rw [ex158x0_apply]; positivity, le_rfl⟩
  have hfirm := hφ.2 () _ hY
  beta_reduce at hfirm
  rw [map_sub, map_smul, smul_eq_mul, ex158x0_apply] at hfirm
  have hge : 0 ≤ φ (ex158e t) := by
    by_contra hneg
    push Not at hneg
    nlinarith
  -- the consumer: cost minimisation over the weakly preferred set
  have hlow : ∀ s, 1 ≤ (ex158x0 - (1 / ((t : ℝ) + 1)) • ex158e t) s := fun s => by
    rw [ex158x0_sub_single_apply]
    split_ifs
    · rw [ex158x0_apply]
      linarith
    · rw [ex158x0_apply]
      have : (0 : ℝ) ≤ 1 / ((s : ℝ) + 1) := by positivity
      linarith
  have hX : ex158x0 - (1 / ((t : ℝ) + 1)) • ex158e t ∈ ex158X () := fun s =>
    le_trans zero_le_one (hlow s)
  have hcons := hφ.1 () _ hX (by beta_reduce; rw [ex158U_x0]; exact le_ex158U hlow)
  beta_reduce at hcons
  rw [map_sub, map_smul, smul_eq_mul] at hcons
  have hle : φ (ex158e t) ≤ 0 := by
    by_contra hpos
    push Not at hpos
    nlinarith
  linarith

/-- **No inner-product representation** (§15.3 (4), p. 461): no nonzero `φ` satisfying (2) and
(3) has the form `φ(x) = Σ_t p_t x_t` for all `x ∈ ℓ_∞`. -/
theorem ex158_no_inner_product {φ : StrongDual ℝ (lp (fun _ : ℕ => ℝ) ∞)} (hφ0 : φ ≠ 0)
    (hφ : SupportsAllocation ex158X ex158U ex158Y (fun _ => ex158x0) (fun _ => ex158x0) φ) :
    ¬ ∃ p : ℕ → ℝ, ∀ x : lp (fun _ : ℕ => ℝ) ∞, HasSum (fun t => p t * x t) (φ x) := by
  rintro ⟨p, hp⟩
  have hpt : ∀ t, p t = 0 := fun t => by
    have h1 := hp (ex158e t)
    have h2 : HasSum (fun s => p s * (ex158e t) s) (p t) := by
      convert hasSum_single t (f := fun s => p s * (ex158e t) s) (fun s hs => by
        simp [ex158e_apply, hs]) using 1
      simp [ex158e_apply]
    rw [← h1.unique h2, ex158_price_vanishes_single hφ t]
  refine hφ0 (ContinuousLinearMap.ext fun x => ?_)
  have := hp x
  simp only [hpt, zero_mul] at this
  rw [zero_apply]
  exact this.unique hasSum_zero

/-! ### Exercise 15.9 and the weighted norm (5) -/

/-- The distance of the weighted norm §15.3 (5): `Σ_t β^t |x_t − x′_t|`. -/
noncomputable def weightedDist (β : ℝ) (x x' : ℕ → ℝ) : ℝ := ∑' t, β ^ t * |x t - x' t|

/-- The weighted distance between sequences that differ only at `T`. -/
theorem weightedDist_update (β : ℝ) (x : ℕ → ℝ) (T : ℕ) (a : ℝ) :
    weightedDist β x (Function.update x T a) = β ^ T * |x T - a| := by
  rw [weightedDist, tsum_eq_single T fun t ht => by simp [Function.update_of_ne ht]]
  simp

/-- Summability (membership of the space with norm (5)) is preserved by changing one
coordinate. -/
theorem summable_weighted_update {β : ℝ} {x : ℕ → ℝ} (hx : Summable fun t => β ^ t * |x t|)
    (T : ℕ) (a : ℝ) : Summable fun t => β ^ t * |Function.update x T a t| := by
  have : (fun t => β ^ t * |Function.update x T a t|) =
      Function.update (fun t => β ^ t * |x t|) T (β ^ T * |a|) := by
    funext t
    rcases eq_or_ne t T with rfl | ht
    · simp
    · simp [Function.update_of_ne ht]
  rw [this]
  exact hx.update T _

/-- **Exercise 15.9** (p. 462): `u(x) = inf_t x_t` is not continuous at `1 = (1, 1, …)` on the
positive orthant of the space with norm (5), `Σ_t β^t |x_t| < ∞`: for `ε = 1/2` and every
`δ > 0`, lowering one far-out coordinate to `1/2` gives `x′` within `δ` of `1` with
`|u(1) − u(x′)| = 1/2`. -/
theorem ex_15_9 {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Summable (fun t => β ^ t * |(1 : ℝ)|) ∧
    ∃ ε > 0, ∀ δ > 0, ∃ x' : ℕ → ℝ, (∀ t, 0 ≤ x' t) ∧ Summable (fun t => β ^ t * |x' t|) ∧
      weightedDist β (fun _ => 1) x' < δ ∧ ε ≤ |(⨅ _ : ℕ, (1 : ℝ)) - ⨅ t, x' t| := by
  have hgeo : Summable fun t : ℕ => β ^ t * |(1 : ℝ)| := by
    simpa using summable_geometric_of_lt_one hβ0.le hβ1
  refine ⟨hgeo, 1 / 2, by norm_num, fun δ hδ => ?_⟩
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hδ hβ1
  set x' := Function.update (fun _ : ℕ => (1 : ℝ)) T (1 / 2) with hx'
  have hcoord : ∀ t, 1 / 2 ≤ x' t := fun t => by
    rcases eq_or_ne t T with rfl | ht
    · simp [hx']
    · norm_num [hx', Function.update_of_ne ht]
  refine ⟨x', fun t => le_trans (by norm_num) (hcoord t), summable_weighted_update hgeo T _, ?_,
    ?_⟩
  · rw [hx', weightedDist_update]
    norm_num
    linarith [pow_pos hβ0 T]
  · have hinf : ⨅ t, x' t = 1 / 2 := le_antisymm
      (by
        have := ciInf_le (⟨1 / 2, by rintro _ ⟨t, rfl⟩; exact hcoord t⟩ :
          BddBelow (range x')) T
        simpa [hx'] using this)
      (le_ciInf hcoord)
    rw [ciInf_const, hinf]
    norm_num [abs_of_pos]

/-- **NOTE to p. 462**: in the norm (5) no point `x` of the positive orthant is interior: for every
`δ > 0` some `z` of the space within distance `δ` of `x` has a negative coordinate. -/
theorem weighted_orthant_no_interior {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x : ℕ → ℝ}
    (hx : Summable fun t => β ^ t * |x t|) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z : ℕ → ℝ, Summable (fun t => β ^ t * |z t|) ∧ weightedDist β x z < δ ∧ ∃ t, z t < 0 := by
  have h1 : ∀ᶠ t in atTop, β ^ t * |x t| < δ / 2 :=
    Filter.Tendsto.eventually_lt_const (by linarith) hx.tendsto_atTop_zero
  have h2 : ∀ᶠ t in atTop, β ^ t < δ / 2 :=
    Filter.Tendsto.eventually_lt_const (by linarith)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1)
  obtain ⟨T, hT1, hT2⟩ := (h1.and h2).exists
  refine ⟨Function.update x T (x T - (|x T| + 1)), summable_weighted_update hx T _, ?_, T, ?_⟩
  · rw [weightedDist_update, sub_sub_cancel, abs_of_pos (by positivity), mul_add, mul_one]
    linarith
  · simp only [Function.update_self]
    linarith [le_abs_self (x T)]

/-- Consequently, in the norm (5) no subset of the positive orthant (for instance the
technology `Y = {0 ≤ y_t ≤ 1 + 1/t}`) has an interior point, so Assumption 15.5 fails there. -/
theorem weighted_no_interior_of_subset_orthant {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {B : Set (ℕ → ℝ)} (hB : ∀ y ∈ B, ∀ t, 0 ≤ y t) {x : ℕ → ℝ}
    (hx : Summable fun t => β ^ t * |x t|) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z : ℕ → ℝ, Summable (fun t => β ^ t * |z t|) ∧ weightedDist β x z < δ ∧ z ∉ B := by
  obtain ⟨z, hz, hd, t, ht⟩ := weighted_orthant_no_interior hβ0 hβ1 hx hδ
  exact ⟨z, hz, hd, fun hzB => (hB z hzB t).not_gt ht⟩

/-- **NOTE to p. 462** (indexing): the state probabilities `(1 − β)β^t` sum to `1` over
`t = 0, 1, 2, …`; with the example's periods `t = 1, 2, …` they must be `(1 − β)β^{t−1}`. -/
theorem hasSum_state_probabilities {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    HasSum (fun t : ℕ => (1 - β) * β ^ t) 1 := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left (1 - β)
  rwa [mul_inv_cancel₀ (by linarith)] at h

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Dual spaces and the Hahn–Banach theorem

SLP §15.1, pp. 445–451 (and one remark from the chapter introduction, p. 444). `S` is a real
normed space and `S*` is `StrongDual ℝ S`, the continuous linear functionals with the operator
norm. The sequence spaces are Mathlib's `lp`: `ellInfSp = ℓ∞`, `ellOneSp = ℓ₁`, `ellTwoSp = ℓ₂`
(sequences indexed by `ℕ`). `L_p(Z, 𝒵, μ)` is `MeasureTheory.Lp ℝ p μ`.

* **Theorem 15.1** (p. 446). The book's continuity is sequential (`SeqContAt`).
  (a) `theorem_15_1a`: a linear functional continuous at one point is continuous at every point.
  (b) `theorem_15_1b`: it is continuous iff it is bounded, `|φ x| ≤ M ‖x‖`.
  `continuous_iff_seqContAt` links the book's continuity with Mathlib's.
  `dual_norm_eq`: the dual norm (1) is the infimum of the bounds, equals the supremum of `|φ x|`
  over the unit sphere, and is itself a bound.
* **Exercise 15.1** (`ex_15_1`, p. 447): `S*` is complete.
* **Example 1** (`example_15_1`, p. 447): `y ↦ (x ↦ y · x)` is an isometric isomorphism from
  `ℝⁿ` onto `(ℝⁿ)*`.
* **Exercise 15.2** (p. 448). (a) `ex_15_2a`: `ℓ₂* = ℓ₂` and (b) `ex_15_2b`: `ℓ₁* = ℓ∞`. In both,
  `y ↦ (x ↦ Σ yᵢ xᵢ)` is an isometric isomorphism onto the dual.
* **Example 2** (`example_15_2`, p. 448): for `1 < p < ∞` and `1/p + 1/q = 1`,
  `y ↦ (x ↦ Σ yᵢ xᵢ)` is an isometric isomorphism from `ℓ_q` onto `ℓ_p*` (`dualEllP`). The
  test vectors `sgn(yᵢ)|yᵢ|^{q−1}` give `‖y‖_q ≤ ‖φ‖` (`sum_rpow_le_of_dual_ellP`).
* **Exercise 15.3** (`ex_15_3`, p. 448): each `y ∈ ℓ₁` gives a continuous linear functional
  `x ↦ Σ yᵢ xᵢ` on `ℓ∞`, of norm `≤ ‖y‖₁`.
* **Exercise 15.4** (p. 448). `cZero` is `c₀` as a subspace of `ℓ∞`, so it is a normed space with
  the sup norm. (a) `ex_15_4a`: it is closed, hence complete. (b) `ex_15_4b`: `c₀* = ℓ₁`, again
  by an isometric isomorphism `y ↦ (x ↦ Σ yᵢ xᵢ)`.
* **Exercise 15.5** (p. 450). (a) `ex_15_5a`: each `f ∈ L₁` gives `φ(x) = ∫ f x dμ` in `L∞*`, of
  norm `≤ ‖f‖₁`. (b) `ex_15_5b`: the same `φ` is `x ↦ ∫ x dν` for the signed measure
  `ν = f μ`, which is absolutely continuous with respect to `μ`.
* **`L₁* = L∞`** (p. 449). `l1_dual_sigmaFinite`: for a σ-finite measure,
  `y ↦ (x ↦ ∫ y x dμ)` is an isometric isomorphism from `L∞` onto `L₁*` (`dualL1`). The proof
  (`exists_preimage_pairLinfL1`) applies Riesz representation in `L₂` to `x ↦ φ(√w x)`, where
  `w > 0` is integrable.
* **Example (p. 450)** (`example_15_4_linf_nat`): if `ν` is a finite measure on `ℕ` with
  `ν {n} > 0` for all `n`, then `L∞(ℕ, ν) ≅ ℓ∞` isometrically.
* **Theorem 15.2** (`theorem_15_2`, the geometric Hahn–Banach theorem, pp. 450–451), with the
  nonemptiness hypotheses added. The two cases are `theorem_15_2_interior` and
  `theorem_15_2_finiteDimensional`.
* **Exercise 15.6** (`ex_15_6`, p. 451): in `S = {x : Σ βᵗ |xₜ| < ∞}`, every ball about `θ` has
  points outside the box `B = {|xₜ| ≤ 1}`. `weightToEllOne` maps `S` isometrically onto `ℓ₁`,
  `xₜ ↦ βᵗ xₜ`, and maps `B` onto `ex156Box β = {z : |zₜ| ≤ βᵗ}`. On that side,
  `interior_ex156Box` shows `B̊ = ∅`, `eq_zero_of_le_zero_on_ex156Box` shows that only `φ = 0` is
  `≤ 0` on `B`, and `ex_15_6_no_separation` shows that Theorem 15.2 fails for `A = {θ}` and this
  `B`, although `A ∩ B̊ = ∅`.

**Corrections.**
* p. 444: convex upper contour sets do not make `U` concave. `intro_concavity_counterexample`:
  `U(l, c) = l³` is quasi-concave on `ℝ²` (all upper contour sets are convex) but not concave.
  Only quasi-concavity is needed.
* p. 445, (1): over `S = {θ}` the unit sphere is empty. With Mathlib's `sSup ∅ = 0` the formula
  still holds (`dual_norm_eq` has no nontriviality hypothesis).
* p. 446: the proof of Theorem 15.1(b) needs `|φ(x)| ≤ 1`, not `φ(x) ≤ 1`. The bound used in
  `theorem_15_1b` is on `|φ x|`.
* p. 449: `L₁(Z, 𝒵, μ)* = L∞(Z, 𝒵, μ)` is false without σ-finiteness. `l1_dual_counterexample`:
  for one point of mass `∞` (`infAtom`), `L₁ = {0}` and `L∞ ≅ ℝ`, so there is no linear
  isomorphism `L∞ ≃ L₁*`. `l1_dual_pairing_counterexample`: the map `y ↦ (x ↦ ∫ y x)` is not
  injective there. Corrected statement: `l1_dual_sigmaFinite`.
* p. 450: "`μ(A) > 0` for all `A ∈ 𝒵`" is impossible, since `μ(∅) = 0`
  (`positive_measure_counterexample`). It must say all nonempty `A`.
* p. 450, Theorem 15.2: `A` must be nonempty, and in the finite-dimensional case `B` too.
  `theorem_15_2_counterexample`: the book's statement (`BookTheorem15_2`) fails on `ℝ` with
  `A = ∅`, `B = ℝ`. `theorem_15_2_counterexample_finiteDimensional`: `A = ℝ`, `B = ∅` satisfy
  the finite-dimensional hypotheses, but no nonzero functional separates them. Corrected
  statement: `theorem_15_2`.
* Manual, Exercise 15.3: the manual gets the convergence of `Σ yₙ xₙ` from convergence of `Σ yₙ`
  and boundedness of `x`. That is not enough (`ex_15_3_manual_counterexample`:
  `yₙ = (−1)ⁿ/(n+1)`, `xₙ = (−1)ⁿ`). The proof here uses absolute summability, `Σ |yₙ| < ∞`
  (`summable_mul_of_one_inf`).
* Manual, Exercise 15.5(b): the manual never checks that `ν` represents `φ`. `ex_15_5b` proves
  `φ(x) = ∫ x dν`, using Mathlib's integral against a signed measure.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Metric Set MeasureTheory
open scoped ENNReal Pointwise symmDiff

/-! ### Theorem 15.1 and Exercise 15.1 -/

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The book's continuity at a point (p. 445): `xₙ → s` implies `f(xₙ) → f(s)`. -/
def SeqContAt (f : S → ℝ) (s : S) : Prop :=
  ∀ xs : ℕ → S, Tendsto xs atTop (𝓝 s) → Tendsto (fun n => f (xs n)) atTop (𝓝 (f s))

/-- **Theorem 15.1(a)**: a linear functional continuous at one point `s` is continuous at every
point. The proof is the book's, with `sₙ = s + xₙ − x`. -/
theorem theorem_15_1a (φ : S →ₗ[ℝ] ℝ) {s : S} (h : SeqContAt φ s) (x : S) : SeqContAt φ x := by
  intro xs hxs
  have hs : Tendsto (fun n => s + xs n - x) atTop (𝓝 s) := by
    have := (tendsto_const_nhds (x := s)).add (hxs.sub (tendsto_const_nhds (x := x)))
    simpa [add_sub_assoc] using this
  have h1 := ((h _ hs).add (tendsto_const_nhds (x := φ x))).sub (tendsto_const_nhds (x := φ s))
  have e : ∀ n, φ (s + xs n - x) + φ x - φ s = φ (xs n) := fun n => by
    rw [map_sub, map_add]; ring
  simpa [e] using h1

/-- On a normed space the book's (sequential) continuity at every point is ordinary
continuity. -/
theorem continuous_iff_seqContAt (φ : S →ₗ[ℝ] ℝ) : Continuous φ ↔ ∀ x, SeqContAt φ x := by
  rw [continuous_iff_seqContinuous]
  exact ⟨fun h x xs hxs => h hxs, fun h x p hx => h p x hx⟩

/-- **Theorem 15.1(b)**: a linear functional is continuous iff it is bounded. -/
theorem theorem_15_1b (φ : S →ₗ[ℝ] ℝ) :
    (∀ x, SeqContAt φ x) ↔ ∃ M, 0 ≤ M ∧ ∀ x, |φ x| ≤ M * ‖x‖ := by
  rw [← continuous_iff_seqContAt]
  constructor
  · intro hc
    let ψ : StrongDual ℝ S := ⟨φ, hc⟩
    exact ⟨‖ψ‖, norm_nonneg _, fun x => ψ.le_opNorm x⟩
  · rintro ⟨M, -, hM⟩
    exact AddMonoidHomClass.continuous_of_bound φ M fun x => hM x

/-- The dual norm (1), p. 445: `‖φ‖` is the infimum of the bounds `M ≥ 0`, equals the supremum
of `|φ x|` over the unit sphere, and is itself a bound. -/
theorem dual_norm_eq (φ : StrongDual ℝ S) :
    ‖φ‖ = sInf {M | 0 ≤ M ∧ ∀ x, |φ x| ≤ M * ‖x‖} ∧
      ‖φ‖ = sSup ((fun x => |φ x|) '' sphere (0 : S) 1) ∧ ∀ x, |φ x| ≤ ‖φ‖ * ‖x‖ := by
  refine ⟨by simp [ContinuousLinearMap.norm_def, Real.norm_eq_abs], ?_,
    fun x => by simpa using φ.le_opNorm x⟩
  simpa [Real.norm_eq_abs] using (φ.sSup_sphere_eq_norm).symm

/-- **Exercise 15.1**: the dual `S*`, with the norm (1), is complete (even if `S` is not). -/
theorem ex_15_1 : CompleteSpace (StrongDual ℝ S) := inferInstance

/-! ### The introduction (p. 444) -/

/-- **Correction (p. 444)**: convex upper contour sets do not give concavity. `U(l, c) = l³` is
quasi-concave on `ℝ²` but not concave. -/
theorem intro_concavity_counterexample :
    QuasiconcaveOn ℝ univ (fun p : ℝ × ℝ => p.1 ^ 3) ∧
      ¬ ConcaveOn ℝ univ (fun p : ℝ × ℝ => p.1 ^ 3) := by
  have hmono : Monotone (fun x : ℝ => x ^ 3) := (Odd.strictMono_pow (by decide)).monotone
  refine ⟨fun r => ?_, fun h => ?_⟩
  · intro p hp q hq a b ha hb hab
    refine ⟨trivial, ?_⟩
    have h1 : min p.1 q.1 ≤ a * p.1 + b * q.1 := by
      calc min p.1 q.1 = a * min p.1 q.1 + b * min p.1 q.1 := by rw [← add_mul, hab, one_mul]
        _ ≤ a * p.1 + b * q.1 := add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hb)
    have h2 : r ≤ (min p.1 q.1) ^ 3 := by
      rcases min_choice p.1 q.1 with h | h <;> rw [h]
      exacts [hp.2, hq.2]
    exact h2.trans (by simpa using hmono h1)
  · have := h.2 (mem_univ ((0 : ℝ), (0 : ℝ))) (mem_univ ((2 : ℝ), (0 : ℝ)))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    norm_num at this

/-! ### Example 1: `ℝⁿ` -/

/-- **Example 1** (p. 447): `y ↦ (x ↦ Σ yᵢ xᵢ)` is an isometric isomorphism from `ℝⁿ` (Euclidean
norm) onto its dual. -/
theorem example_15_1 (n : ℕ) :
    ∃ e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] StrongDual ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ y x, e y x = ∑ i, y i * x i := by
  let T : EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] StrongDual ℝ (EuclideanSpace ℝ (Fin n)) :=
    { toFun := fun y => InnerProductSpace.toDual ℝ _ y
      map_add' := fun y z => map_add _ y z
      map_smul' := fun c y => by ext; simp
      norm_map' := fun y => LinearIsometryEquiv.norm_map _ y }
  refine ⟨LinearIsometryEquiv.ofSurjective T fun φ =>
    ⟨(InnerProductSpace.toDual ℝ _).symm φ, by simp [T]⟩, fun y x => ?_⟩
  change InnerProductSpace.toDual ℝ _ y x = _
  rw [InnerProductSpace.toDual_apply_apply, PiLp.inner_apply]
  simp [mul_comm]

/-! ### Sequence spaces: Exercises 15.2 and 15.3 -/

/-- `ℓ∞`: bounded real sequences with the sup norm. -/
abbrev ellInfSp := lp (fun _ : ℕ => ℝ) ∞

/-- `ℓ₁`: absolutely summable real sequences. -/
abbrev ellOneSp := lp (fun _ : ℕ => ℝ) 1

/-- `ℓ₂`: square-summable real sequences. -/
abbrev ellTwoSp := lp (fun _ : ℕ => ℝ) 2

/-- The pairing `(y, x) ↦ Σ yᵢ xᵢ` of `ℓ∞` with `ℓ₁` (Mathlib's `lp.dualPairing`). -/
noncomputable def pairInfOne : ellInfSp →L[ℝ] ellOneSp →L[ℝ] ℝ :=
  lp.dualPairing ∞ 1 (fun _ => ContinuousLinearMap.mul ℝ ℝ) (K := 1)
    (fun _ => ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

/-- The pairing `(y, x) ↦ Σ yᵢ xᵢ` of `ℓ₁` with `ℓ∞`. -/
noncomputable def pairOneInf : ellOneSp →L[ℝ] ellInfSp →L[ℝ] ℝ :=
  lp.dualPairing 1 ∞ (fun _ => ContinuousLinearMap.mul ℝ ℝ) (K := 1)
    (fun _ => ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

/-- The pairing `(y, x) ↦ Σ yᵢ xᵢ` of `ℓ₂` with itself. -/
noncomputable def pairTwo : ellTwoSp →L[ℝ] ellTwoSp →L[ℝ] ℝ :=
  lp.dualPairing 2 2 (fun _ => ContinuousLinearMap.mul ℝ ℝ) (K := 1)
    (fun _ => ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

/-- `pairInfOne y x = Σ yᵢ xᵢ`. -/
theorem pairInfOne_apply (y : ellInfSp) (x : ellOneSp) : pairInfOne y x = ∑' i, y i * x i := rfl

/-- `pairOneInf y x = Σ yᵢ xᵢ`. -/
theorem pairOneInf_apply (y : ellOneSp) (x : ellInfSp) : pairOneInf y x = ∑' i, y i * x i := rfl

/-- `pairTwo y x = Σ yᵢ xᵢ`. -/
theorem pairTwo_apply (y x : ellTwoSp) : pairTwo y x = ∑' i, y i * x i := rfl

/-- Hölder's inequality for `ℓ∞ × ℓ₁`: the pairing has norm `≤ 1`. -/
theorem norm_pairInfOne_le : ‖pairInfOne‖ ≤ 1 :=
  (lp.norm_dualPairing (ι := ℕ) (E := fun _ => ℝ) (F := fun _ => ℝ) (p := ∞) (q := 1) _ _).trans
    (by simp)

/-- Hölder's inequality for `ℓ₁ × ℓ∞`: the pairing has norm `≤ 1`. -/
theorem norm_pairOneInf_le : ‖pairOneInf‖ ≤ 1 :=
  (lp.norm_dualPairing (ι := ℕ) (E := fun _ => ℝ) (F := fun _ => ℝ) (p := 1) (q := ∞) _ _).trans
    (by simp)

/-- The unit sequence `eᵢ` has norm `1` in every `ℓ_p`. -/
theorem norm_single_one {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : ℕ) :
    ‖lp.single (E := fun _ : ℕ => ℝ) p i (1 : ℝ)‖ = 1 := by
  rw [lp.norm_single (zero_lt_one.trans_le Fact.out)]; simp

/-- `Σⱼ yⱼ (a eᵢ)ⱼ = yᵢ a`. -/
theorem tsum_mul_single (y : ℕ → ℝ) (i : ℕ) (a : ℝ) :
    ∑' j, y j * (Pi.single i a : ℕ → ℝ) j = y i * a := by
  rw [tsum_eq_single i]
  · simp
  · intro j hj; simp [hj]

/-- The `ℓ₁` norm is `Σ |yᵢ|`. -/
theorem norm_ellOneSp_eq_tsum (y : ellOneSp) : ‖y‖ = ∑' i, |y i| := by
  rw [lp.norm_eq_tsum_rpow (by simp)]; simp

/-- An element of `ℓ₁` is absolutely summable. -/
theorem summable_abs_ellOneSp (y : ellOneSp) : Summable fun i => |y i| := by
  simpa using (lp.memℓp y).summable (p := 1) (by simp)

/-- For `y ∈ ℓ₁` and bounded `x`, `Σ yᵢ xᵢ` converges absolutely. This uses `Σ |yᵢ| < ∞`, not
just convergence of `Σ yᵢ` (see `ex_15_3_manual_counterexample`). -/
theorem summable_mul_of_one_inf (y : ellOneSp) (x : ellInfSp) : Summable fun i => y i * x i := by
  refine Summable.of_norm_bounded ((summable_abs_ellOneSp y).mul_right ‖x‖) fun i => ?_
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by simp) x i) (abs_nonneg _)

/-- **Exercise 15.3**: each `y ∈ ℓ₁` defines a continuous linear functional `x ↦ Σ yᵢ xᵢ` on
`ℓ∞`, with norm at most `‖y‖₁`. -/
theorem ex_15_3 (y : ellOneSp) :
    (∀ x : ellInfSp, Summable fun i => y i * x i) ∧
      ∃ φ : StrongDual ℝ ellInfSp, (∀ x, φ x = ∑' i, y i * x i) ∧ ‖φ‖ ≤ ‖y‖ := by
  refine ⟨summable_mul_of_one_inf y, pairOneInf y, fun x => rfl, ?_⟩
  calc ‖pairOneInf y‖ ≤ ‖pairOneInf‖ * ‖y‖ := pairOneInf.le_opNorm y
    _ ≤ 1 * ‖y‖ := by gcongr; exact norm_pairOneInf_le
    _ = ‖y‖ := one_mul _

/-- **Correction (manual, Exercise 15.3)**: convergence of `Σ yₙ` together with `|xₙ| ≤ 1` does
not make `Σ yₙ xₙ` converge (`yₙ = (−1)ⁿ/(n+1)`, `xₙ = (−1)ⁿ`). -/
theorem ex_15_3_manual_counterexample :
    ∃ y x : ℕ → ℝ, (∃ l, Tendsto (fun N => ∑ n ∈ Finset.range N, y n) atTop (𝓝 l)) ∧
      (∀ n, |x n| ≤ 1) ∧
      ¬ ∃ l, Tendsto (fun N => ∑ n ∈ Finset.range N, y n * x n) atTop (𝓝 l) := by
  refine ⟨fun n => (-1) ^ n * (1 / ((n : ℝ) + 1)), fun n => (-1) ^ n, ?_, fun n => by simp, ?_⟩
  · refine Antitone.tendsto_alternating_series_of_tendsto_zero ?_ ?_
    · intro m n hmn
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      dsimp only
      gcongr
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · rintro ⟨l, hl⟩
    have e : ∀ n : ℕ, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1)) * (-1) ^ n = 1 / ((n : ℝ) + 1) :=
      fun n => by
        rw [mul_comm, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
    simp only [e] at hl
    exact not_tendsto_nhds_of_tendsto_atTop Real.tendsto_sum_range_one_div_nat_succ_atTop l hl

/-- `y ↦ (x ↦ Σ yᵢ xᵢ)` preserves norms from `ℓ∞` to `ℓ₁*`. -/
theorem norm_pairInfOne (y : ellInfSp) : ‖pairInfOne y‖ = ‖y‖ := by
  apply le_antisymm
  · calc ‖pairInfOne y‖ ≤ ‖pairInfOne‖ * ‖y‖ := pairInfOne.le_opNorm y
      _ ≤ 1 * ‖y‖ := by gcongr; exact norm_pairInfOne_le
      _ = ‖y‖ := one_mul _
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun i => ?_
    have h := (pairInfOne y).le_opNorm (lp.single 1 i 1)
    rw [norm_single_one, mul_one, pairInfOne_apply, lp.coeFn_single, tsum_mul_single,
      mul_one] at h
    exact h

/-- Every `φ ∈ ℓ₁*` is `x ↦ Σ yᵢ xᵢ` with `yᵢ = φ(eᵢ)`. -/
theorem pairInfOne_surjective : Function.Surjective pairInfOne := by
  intro φ
  let y : ellInfSp := ⟨fun i => φ (lp.single 1 i 1), memℓp_infty_iff.2 ⟨‖φ‖, by
    rintro _ ⟨i, rfl⟩
    simpa [norm_single_one] using φ.le_opNorm (lp.single 1 i 1)⟩⟩
  refine ⟨y, lp.ext_continuousLinearMap (by simp) fun i => ?_⟩
  ext
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rw [pairInfOne_apply, lp.coeFn_single, tsum_mul_single, mul_one]

/-- `ℓ₁* = ℓ∞` as normed spaces. -/
noncomputable def dualEllOne : ellInfSp ≃ₗᵢ[ℝ] StrongDual ℝ ellOneSp :=
  LinearIsometryEquiv.ofSurjective ⟨pairInfOne.toLinearMap, norm_pairInfOne⟩ pairInfOne_surjective

/-- **Exercise 15.2(b)**: the dual of `ℓ₁` is `ℓ∞`. Each `y ∈ ℓ∞` gives `x ↦ Σ yᵢ xᵢ` in `ℓ₁*`,
every element of `ℓ₁*` arises from exactly one `y`, and norms are preserved. -/
theorem ex_15_2b :
    ∃ e : ellInfSp ≃ₗᵢ[ℝ] StrongDual ℝ ellOneSp, ∀ y x, e y x = ∑' i, y i * x i :=
  ⟨dualEllOne, fun _ _ => rfl⟩

/-- On `ℓ₂` the pairing is the Riesz map `y ↦ ⟪y, ·⟫`. -/
theorem pairTwo_eq_toDual (y : ellTwoSp) : pairTwo y = InnerProductSpace.toDual ℝ ellTwoSp y := by
  ext x
  rw [InnerProductSpace.toDual_apply_apply, lp.inner_eq_tsum]
  change ∑' i, y i * x i = _
  congr 1
  ext i
  simp [mul_comm]

/-- `y ↦ (x ↦ Σ yᵢ xᵢ)` preserves norms on `ℓ₂`. -/
theorem norm_pairTwo (y : ellTwoSp) : ‖pairTwo y‖ = ‖y‖ := by
  rw [pairTwo_eq_toDual, LinearIsometryEquiv.norm_map]

/-- Every `φ ∈ ℓ₂*` is `x ↦ Σ yᵢ xᵢ` for some `y ∈ ℓ₂` (Riesz representation). -/
theorem pairTwo_surjective : Function.Surjective pairTwo := fun φ =>
  ⟨(InnerProductSpace.toDual ℝ ellTwoSp).symm φ, by rw [pairTwo_eq_toDual]; simp⟩

/-- `ℓ₂* = ℓ₂` as normed spaces. -/
noncomputable def dualEllTwo : ellTwoSp ≃ₗᵢ[ℝ] StrongDual ℝ ellTwoSp :=
  LinearIsometryEquiv.ofSurjective ⟨pairTwo.toLinearMap, norm_pairTwo⟩ pairTwo_surjective

/-- **Exercise 15.2(a)**: the dual of `ℓ₂` is `ℓ₂`, with `y` acting by `x ↦ Σ yᵢ xᵢ`. -/
theorem ex_15_2a :
    ∃ e : ellTwoSp ≃ₗᵢ[ℝ] StrongDual ℝ ellTwoSp, ∀ y x, e y x = ∑' i, y i * x i :=
  ⟨dualEllTwo, fun _ _ => rfl⟩

/-! ### Example 2: `ℓ_p* = ℓ_q` for `1 < p < ∞` -/

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The pairing `(y, x) ↦ Σ yᵢ xᵢ` of `ℓ_q` with `ℓ_p` (Mathlib's `lp.dualPairing`). -/
noncomputable def pairEllP (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] :
    lp (fun _ : ℕ => ℝ) q →L[ℝ] lp (fun _ : ℕ => ℝ) p →L[ℝ] ℝ :=
  lp.dualPairing q p (fun _ => ContinuousLinearMap.mul ℝ ℝ) (K := 1)
    (fun _ => ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

/-- `pairEllP p q y x = Σ yᵢ xᵢ`. -/
theorem pairEllP_apply (y : lp (fun _ : ℕ => ℝ) q) (x : lp (fun _ : ℕ => ℝ) p) :
    pairEllP p q y x = ∑' i, y i * x i := rfl

/-- Hölder's inequality for `ℓ_q × ℓ_p`: the pairing has norm `≤ 1`. -/
theorem norm_pairEllP_le : ‖pairEllP p q‖ ≤ 1 :=
  (lp.norm_dualPairing (ι := ℕ) (E := fun _ => ℝ) (F := fun _ => ℝ) (p := q) (q := p) _ _).trans
    (by simp)

omit [Fact (1 ≤ q)] in
/-- For `φ ∈ ℓ_p*` and `yᵢ = φ(eᵢ)`, `Σ_{i<N} |yᵢ|^q ≤ ‖φ‖^q`. The test vector is
`xᵢ = sgn(yᵢ) |yᵢ|^{q−1}` for `i < N`, which has `φ(x) = Σ_{i<N} |yᵢ|^q = ‖x‖_p^p`. -/
theorem sum_rpow_le_of_dual_ellP (hp : p ≠ ∞) (hq : q ≠ ∞)
    (φ : StrongDual ℝ (lp (fun _ : ℕ => ℝ) p)) (N : ℕ) :
    ∑ i ∈ Finset.range N, |φ (lp.single p i 1)| ^ q.toReal ≤ ‖φ‖ ^ q.toReal := by
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  set P := p.toReal
  set Q := q.toReal
  set y : ℕ → ℝ := fun i => φ (lp.single p i 1) with hy
  have hQ1 : 0 < Q - 1 := hPQ.symm.sub_one_pos
  have hQP : (Q - 1) * P = Q := hPQ.symm.sub_one_mul_conj
  let a : ℕ → ℝ := fun i => if 0 ≤ y i then |y i| ^ (Q - 1) else -(|y i| ^ (Q - 1))
  set S := ∑ i ∈ Finset.range N, |y i| ^ Q
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hay : ∀ i, a i * y i = |y i| ^ Q := fun i => by
    have e : |y i| ^ Q = |y i| ^ (Q - 1) * |y i| := by
      conv_lhs => rw [show Q = (Q - 1) + 1 by ring]
      rw [Real.rpow_add' (abs_nonneg _) (by linarith), Real.rpow_one]
    rw [e]
    simp only [a]
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.1 h)]; ring
  have hna : ∀ i, ‖a i‖ ^ P = |y i| ^ Q := fun i => by
    have : ‖a i‖ = |y i| ^ (Q - 1) := by
      simp only [a]; split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ |y i| ^ (Q - 1))]
    rw [this, ← Real.rpow_mul (abs_nonneg _), hQP]
  set x := ∑ i ∈ Finset.range N, lp.single p i (a i)
  have hφx : φ x = S := by
    simp only [x, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : lp.single p i (a i) = a i • lp.single (E := fun _ : ℕ => ℝ) p i 1 := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul, ← hay i]
  have hxP : ‖x‖ ^ P = S := by
    rw [lp.norm_sum_single hPQ.pos]
    exact Finset.sum_congr rfl fun i _ => hna i
  have hx : ‖x‖ = S ^ (1 / P) := by
    rw [← hxP, ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hPQ.ne_zero, Real.rpow_one]
  have hb : S ≤ ‖φ‖ * S ^ (1 / P) := by
    calc S = φ x := hφx.symm
      _ ≤ ‖φ‖ * ‖x‖ := (le_abs_self _).trans (φ.le_opNorm x)
      _ = ‖φ‖ * S ^ (1 / P) := by rw [hx]
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have hsplit : S = S ^ (1 / P) * S ^ (1 / Q) := by
      have h11 : 1 / P + 1 / Q = 1 := by rw [one_div, one_div, hPQ.inv_add_inv_eq_one]
      rw [← Real.rpow_add hpos, h11, Real.rpow_one]
    have h1 : S ^ (1 / Q) ≤ ‖φ‖ := by
      have hp' : 0 < S ^ (1 / P) := Real.rpow_pos_of_pos hpos _
      nth_rewrite 1 [hsplit] at hb
      rw [mul_comm (S ^ (1 / P)) (S ^ (1 / Q))] at hb
      exact le_of_mul_le_mul_right hb hp'
    calc S = (S ^ (1 / Q)) ^ Q := by
          rw [← Real.rpow_mul hS0, one_div_mul_cancel hPQ.symm.ne_zero, Real.rpow_one]
      _ ≤ ‖φ‖ ^ Q := Real.rpow_le_rpow (by positivity) h1 hPQ.symm.nonneg

/-- For `1 < p < ∞`, every `φ ∈ ℓ_p*` is `x ↦ Σ yᵢ xᵢ` with `yᵢ = φ(eᵢ)`, `y ∈ ℓ_q` and
`‖y‖_q ≤ ‖φ‖`. -/
theorem exists_preimage_pairEllP (hp : p ≠ ∞) (hq : q ≠ ∞)
    (φ : StrongDual ℝ (lp (fun _ : ℕ => ℝ) p)) :
    ∃ y : lp (fun _ : ℕ => ℝ) q, pairEllP p q y = φ ∧ ‖y‖ ≤ ‖φ‖ := by
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hsum : Summable fun i => ‖φ (lp.single p i 1)‖ ^ q.toReal :=
    summable_of_sum_range_le (fun i => by positivity) fun N => by
      simpa [Real.norm_eq_abs] using sum_rpow_le_of_dual_ellP hp hq φ N
  let y : lp (fun _ : ℕ => ℝ) q :=
    ⟨fun i => φ (lp.single p i 1), (memℓp_gen_iff hPQ.symm.pos).2 hsum⟩
  refine ⟨y, lp.ext_continuousLinearMap hp fun i => ?_, ?_⟩
  · ext
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      lp.singleContinuousLinearMap_apply]
    rw [pairEllP_apply, lp.coeFn_single, tsum_mul_single, mul_one]
  · refine lp.norm_le_of_tsum_le hPQ.symm.pos (norm_nonneg _) ?_
    refine Real.tsum_le_of_sum_range_le (fun i => by positivity) fun N => ?_
    simpa [Real.norm_eq_abs] using sum_rpow_le_of_dual_ellP hp hq φ N

/-- `y ↦ (x ↦ Σ yᵢ xᵢ)` preserves norms from `ℓ_q` to `ℓ_p*` (`1 < p < ∞`). -/
theorem norm_pairEllP (hp : p ≠ ∞) (hq : q ≠ ∞) (y : lp (fun _ : ℕ => ℝ) q) :
    ‖pairEllP p q y‖ = ‖y‖ := by
  apply le_antisymm
  · calc ‖pairEllP p q y‖ ≤ ‖pairEllP p q‖ * ‖y‖ := (pairEllP p q).le_opNorm y
      _ ≤ 1 * ‖y‖ := by gcongr; exact norm_pairEllP_le
      _ = ‖y‖ := one_mul _
  · obtain ⟨y', hy', hn⟩ := exists_preimage_pairEllP hp hq (pairEllP p q y)
    have e : y' = y := by
      refine lp.ext (funext fun i => ?_)
      have := congrArg (fun φ => φ (lp.single p i 1)) hy'
      simp only [pairEllP_apply, lp.coeFn_single, tsum_mul_single, mul_one] at this
      exact this
    calc ‖y‖ = ‖y'‖ := by rw [e]
      _ ≤ ‖pairEllP p q y‖ := hn

/-- `ℓ_p* = ℓ_q` as normed spaces, for conjugate `1 < p, q < ∞`. -/
noncomputable def dualEllP (hp : p ≠ ∞) (hq : q ≠ ∞) :
    lp (fun _ : ℕ => ℝ) q ≃ₗᵢ[ℝ] StrongDual ℝ (lp (fun _ : ℕ => ℝ) p) :=
  LinearIsometryEquiv.ofSurjective ⟨(pairEllP p q).toLinearMap, norm_pairEllP hp hq⟩
    fun φ => (exists_preimage_pairEllP hp hq φ).imp fun _ h => h.1

/-- **Example 2** (p. 448): for `1 < p < ∞` and `1/p + 1/q = 1`, the dual of `ℓ_p` is `ℓ_q`.
Each `y ∈ ℓ_q` gives `x ↦ Σ yᵢ xᵢ` in `ℓ_p*`, every element of `ℓ_p*` arises from exactly one
`y`, and norms are preserved. (`p = 1` is `ex_15_2b`.) -/
theorem example_15_2 (hp : p ≠ ∞) (hq : q ≠ ∞) :
    ∃ e : lp (fun _ : ℕ => ℝ) q ≃ₗᵢ[ℝ] StrongDual ℝ (lp (fun _ : ℕ => ℝ) p),
      ∀ y x, e y x = ∑' i, y i * x i :=
  ⟨dualEllP hp hq, fun _ _ => rfl⟩

/-! ### `c₀`: Exercise 15.4 -/

/-- `c₀`: the sequences in `ℓ∞` that tend to `0`, as a subspace of `ℓ∞`. It inherits the sup
norm, so it is a normed space. -/
def cZero : Submodule ℝ ellInfSp where
  carrier := {x | Tendsto (fun n => x n) atTop (𝓝 0)}
  add_mem' {x y} hx hy := by simpa using hx.add hy
  zero_mem' := by simp
  smul_mem' c x hx := by simpa using hx.const_mul c

/-- Membership in `c₀`. -/
theorem mem_cZero {x : ellInfSp} : x ∈ cZero ↔ Tendsto (fun n => x n) atTop (𝓝 0) := Iff.rfl

/-- `c₀` is closed in `ℓ∞`. -/
theorem isClosed_cZero : IsClosed (cZero : Set ellInfSp) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  change Tendsto (fun n => x n) atTop (𝓝 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hy : Tendsto (fun n => y n) atTop (𝓝 0)) (ε / 2)
    (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have h2 : ‖x n - y n‖ ≤ ‖x - y‖ := by
    have := lp.norm_apply_le_norm (p := ∞) (by simp) (x - y) n
    simpa using this
  rw [dist_eq_norm] at hxy
  rw [Real.dist_eq, sub_zero] at h1 ⊢
  rw [Real.norm_eq_abs] at h2
  calc |x n| = |(x n - y n) + y n| := by ring_nf
    _ ≤ |x n - y n| + |y n| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := add_halves ε

/-- **Exercise 15.4(a)**: `c₀` with the sup norm is a normed space (the norm of `x ∈ c₀` is its
norm in `ℓ∞`). It is also closed in `ℓ∞`, so it is complete. -/
theorem ex_15_4a : (∀ x : cZero, ‖x‖ = ‖(x : ellInfSp)‖) ∧ CompleteSpace cZero :=
  ⟨fun _ => rfl, isClosed_cZero.completeSpace_coe⟩

/-- The truncated sign vector `(sgn y₀, …, sgn y_{N−1}, 0, 0, …)`, with `sgn 0 = 1`. -/
noncomputable def signTrunc (y : ℕ → ℝ) (N : ℕ) : ellInfSp :=
  ⟨fun i => if i < N then (if 0 ≤ y i then 1 else -1) else 0, memℓp_infty_iff.2 ⟨1, by
    rintro _ ⟨i, rfl⟩
    dsimp only
    split_ifs <;> simp⟩⟩

/-- The truncated sign vector lies in `c₀`. -/
theorem signTrunc_mem (y : ℕ → ℝ) (N : ℕ) : signTrunc y N ∈ cZero := by
  rw [mem_cZero]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with i hi
  simp [signTrunc, not_lt.2 hi]

/-- The truncated sign vector has sup norm `≤ 1`. -/
theorem norm_signTrunc_le (y : ℕ → ℝ) (N : ℕ) : ‖signTrunc y N‖ ≤ 1 :=
  lp.norm_le_of_forall_le zero_le_one fun i => by
    simp only [signTrunc]
    change ‖(if i < N then (if 0 ≤ y i then (1 : ℝ) else -1) else 0)‖ ≤ 1
    split_ifs <;> simp

/-- `Σ yᵢ (signTrunc y N)ᵢ = Σ_{i<N} |yᵢ|`. -/
theorem tsum_mul_signTrunc (y : ℕ → ℝ) (N : ℕ) :
    ∑' i, y i * signTrunc y N i = ∑ i ∈ Finset.range N, |y i| := by
  rw [tsum_eq_sum (s := Finset.range N)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N := Finset.mem_range.1 hi
    change y i * (if i < N then (if 0 ≤ y i then (1 : ℝ) else -1) else 0) = _
    by_cases h : 0 ≤ y i
    · simp [hi', h, abs_of_nonneg h]
    · simp [hi', h, abs_of_neg (not_le.1 h)]
  · intro i hi
    have hi' : ¬ i < N := fun h => hi (Finset.mem_range.2 h)
    change y i * (if i < N then (if 0 ≤ y i then (1 : ℝ) else -1) else 0) = 0
    simp [hi']

/-- The map `ℓ₁ → c₀*`, `y ↦ (x ↦ Σ yᵢ xᵢ)`. -/
noncomputable def pairOneCZero : ellOneSp →ₗ[ℝ] StrongDual ℝ cZero where
  toFun y := (pairOneInf y).comp cZero.subtypeL
  map_add' y z := by ext; simp
  map_smul' c y := by ext; simp

/-- `pairOneCZero y x = Σ yᵢ xᵢ`. -/
theorem pairOneCZero_apply (y : ellOneSp) (x : cZero) :
    pairOneCZero y x = ∑' i, y i * (x : ellInfSp) i := rfl

/-- `y ↦ (x ↦ Σ yᵢ xᵢ)` preserves norms from `ℓ₁` to `c₀*`. The lower bound uses the
truncated sign vectors, as in the manual. -/
theorem norm_pairOneCZero (y : ellOneSp) : ‖pairOneCZero y‖ = ‖y‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [pairOneCZero_apply, ← pairOneInf_apply]
    calc ‖pairOneInf y (x : ellInfSp)‖ ≤ ‖pairOneInf y‖ * ‖(x : ellInfSp)‖ :=
          (pairOneInf y).le_opNorm _
      _ ≤ (1 * ‖y‖) * ‖x‖ := by
          gcongr
          · exact (pairOneInf.le_opNorm y).trans (by gcongr; exact norm_pairOneInf_le)
          · exact le_rfl
      _ = ‖y‖ * ‖x‖ := by rw [one_mul]
  · rw [norm_ellOneSp_eq_tsum]
    refine (summable_abs_ellOneSp y).tsum_le_of_sum_range_le fun N => ?_
    have h := (pairOneCZero y).le_opNorm ⟨signTrunc y N, signTrunc_mem y N⟩
    rw [pairOneCZero_apply] at h
    change ‖∑' i, y i * signTrunc y N i‖ ≤ _ at h
    rw [tsum_mul_signTrunc] at h
    have h2 : ‖(⟨signTrunc y N, signTrunc_mem y N⟩ : cZero)‖ ≤ 1 := norm_signTrunc_le y N
    calc ∑ i ∈ Finset.range N, |y i| ≤ ‖∑ i ∈ Finset.range N, |y i|‖ := le_abs_self _
      _ ≤ ‖pairOneCZero y‖ * ‖(⟨signTrunc y N, signTrunc_mem y N⟩ : cZero)‖ := h
      _ ≤ ‖pairOneCZero y‖ * 1 := by gcongr
      _ = ‖pairOneCZero y‖ := mul_one _

/-- The unit sequence `eᵢ` as an element of `c₀`. -/
noncomputable def unitCZero (i : ℕ) : cZero :=
  ⟨lp.single ∞ i 1, by
    rw [mem_cZero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop i] with j hj
    simp [lp.single_apply, hj.ne']⟩

/-- In `c₀` (unlike `ℓ∞`), `x = lim_N Σ_{i<N} xᵢ eᵢ` in the sup norm. -/
theorem tendsto_trunc_cZero (x : cZero) :
    Tendsto (fun N => ∑ i ∈ Finset.range N, (x : ellInfSp) i • unitCZero i) atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hx := mem_cZero.1 x.2
  rw [Metric.tendsto_atTop] at hx ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := hx (ε / 2) (half_pos hε)
  refine ⟨N0, fun N hN => ?_⟩
  have key : ‖∑ i ∈ Finset.range N, (x : ellInfSp) i • unitCZero i - x‖ ≤ ε / 2 := by
    change ‖((∑ i ∈ Finset.range N, (x : ellInfSp) i • unitCZero i - x : cZero) :
      ellInfSp)‖ ≤ ε / 2
    rw [Submodule.coe_sub, Submodule.coe_sum]
    refine lp.norm_le_of_forall_le (half_pos hε).le fun j => ?_
    rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply]
    simp only [Submodule.coe_smul, unitCZero, lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_range]
    by_cases hj : j < N
    · simp [hj, (half_pos hε).le]
    · have := hN0 j (hN.trans (not_lt.1 hj))
      rw [Real.dist_eq, sub_zero] at this
      simpa [hj] using this.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact key.trans_lt (half_lt_self hε)

/-- Every `φ ∈ c₀*` is `x ↦ Σ yᵢ xᵢ` with `yᵢ = φ(eᵢ)` and `y ∈ ℓ₁`. -/
theorem pairOneCZero_surjective : Function.Surjective pairOneCZero := by
  intro φ
  obtain ⟨yf, hyf⟩ : ∃ yf : ℕ → ℝ, ∀ i, φ (unitCZero i) = yf i := ⟨_, fun _ => rfl⟩
  have hpart : ∀ N, ∑ i ∈ Finset.range N, |yf i| ≤ ‖φ‖ := fun N => by
    have hz : (⟨signTrunc yf N, signTrunc_mem yf N⟩ : cZero) =
        ∑ i ∈ Finset.range N, (if 0 ≤ yf i then (1 : ℝ) else -1) • unitCZero i := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      ext j
      rw [lp.coeFn_sum, Finset.sum_apply]
      simp only [Submodule.coe_smul, unitCZero, lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
        Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_range]
      rfl
    have h := φ.le_opNorm ⟨signTrunc yf N, signTrunc_mem yf N⟩
    rw [hz, map_sum] at h
    simp only [map_smul, smul_eq_mul, hyf] at h
    have e : ∀ i, (if 0 ≤ yf i then (1 : ℝ) else -1) * yf i = |yf i| := fun i => by
      split_ifs with hi
      · rw [one_mul, abs_of_nonneg hi]
      · rw [neg_one_mul, abs_of_neg (not_le.1 hi)]
    simp only [e] at h
    rw [← hz] at h
    calc ∑ i ∈ Finset.range N, |yf i| ≤ ‖∑ i ∈ Finset.range N, |yf i|‖ := le_abs_self _
      _ ≤ ‖φ‖ * ‖(⟨signTrunc yf N, signTrunc_mem yf N⟩ : cZero)‖ := h
      _ ≤ ‖φ‖ * 1 := by gcongr; exact norm_signTrunc_le yf N
      _ = ‖φ‖ := mul_one _
  have hsum : Summable fun i => |yf i| :=
    summable_of_sum_range_le (fun i => abs_nonneg _) hpart
  let y : ellOneSp := ⟨yf, by
    refine memℓp_gen_iff (p := 1) (by simp) |>.2 ?_
    simpa using hsum⟩
  refine ⟨y, ContinuousLinearMap.ext fun x => ?_⟩
  have h1 := ((pairOneCZero y).continuous.tendsto x).comp (tendsto_trunc_cZero x)
  have h2 := (φ.continuous.tendsto x).comp (tendsto_trunc_cZero x)
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  simp only [Function.comp_apply, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pairOneCZero_apply, hyf i]
  congr 1
  change _ = ∑' j, yf j * (Pi.single i (1 : ℝ) : ℕ → ℝ) j
  rw [tsum_mul_single, mul_one]

/-- `c₀* = ℓ₁` as normed spaces. -/
noncomputable def dualCZero : ellOneSp ≃ₗᵢ[ℝ] StrongDual ℝ cZero :=
  LinearIsometryEquiv.ofSurjective ⟨pairOneCZero, norm_pairOneCZero⟩ pairOneCZero_surjective

/-- **Exercise 15.4(b)**: the dual of `c₀` is `ℓ₁`. Each `y ∈ ℓ₁` gives `x ↦ Σ yᵢ xᵢ` in `c₀*`,
every element of `c₀*` arises from exactly one `y`, and norms are preserved. -/
theorem ex_15_4b :
    ∃ e : ellOneSp ≃ₗᵢ[ℝ] StrongDual ℝ cZero, ∀ y x, e y x = ∑' i, y i * (x : ellInfSp) i :=
  ⟨dualCZero, fun _ _ => rfl⟩

/-! ### `L_p` spaces: Exercise 15.5 and `L₁* = L∞` -/

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

/-- The pairing `(f, x) ↦ ∫ f x dμ` of `L₁` with `L∞` (Mathlib's `lpPairing`). -/
noncomputable def pairL1Linf (μ : Measure Z) : Lp ℝ 1 μ →L[ℝ] Lp ℝ ∞ μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 1 ∞

/-- The pairing `(y, x) ↦ ∫ y x dμ` of `L∞` with `L₁`. -/
noncomputable def pairLinfL1 (μ : Measure Z) : Lp ℝ ∞ μ →L[ℝ] Lp ℝ 1 μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1

/-- `pairL1Linf μ f x = ∫ f x dμ`. -/
theorem pairL1Linf_apply (f : Lp ℝ 1 μ) (x : Lp ℝ ∞ μ) :
    pairL1Linf μ f x = ∫ z, f z * x z ∂μ := by
  rw [pairL1Linf, ContinuousLinearMap.lpPairing_eq_integral]; rfl

/-- `pairLinfL1 μ y x = ∫ y x dμ`. -/
theorem pairLinfL1_apply (y : Lp ℝ ∞ μ) (x : Lp ℝ 1 μ) :
    pairLinfL1 μ y x = ∫ z, y z * x z ∂μ := by
  rw [pairLinfL1, ContinuousLinearMap.lpPairing_eq_integral]; rfl

/-- Hölder's inequality: `|∫ f x dμ| ≤ ‖f‖₁ ‖x‖∞`. -/
theorem abs_pairL1Linf_le (f : Lp ℝ 1 μ) (x : Lp ℝ ∞ μ) :
    |pairL1Linf μ f x| ≤ ‖f‖ * ‖x‖ := by
  have h1 : pairL1Linf μ f x = L1.integral ((ContinuousLinearMap.mul ℝ ℝ).holder 1 f x) := by
    rw [pairL1Linf_apply, L1.integral_eq_integral]
    exact integral_congr_ae ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder f x).symm
  rw [h1, ← Real.norm_eq_abs]
  refine (L1.norm_integral_le _).trans ?_
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le f x).trans ?_
  have := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖f‖ * ‖x‖ ≤ 1 * ‖f‖ * ‖x‖ := by gcongr
    _ = ‖f‖ * ‖x‖ := by rw [one_mul]

/-- Hölder's inequality: `|∫ y x dμ| ≤ ‖y‖∞ ‖x‖₁`. -/
theorem abs_pairLinfL1_le (y : Lp ℝ ∞ μ) (x : Lp ℝ 1 μ) :
    |pairLinfL1 μ y x| ≤ ‖y‖ * ‖x‖ := by
  have h1 : pairLinfL1 μ y x = L1.integral ((ContinuousLinearMap.mul ℝ ℝ).holder 1 y x) := by
    rw [pairLinfL1_apply, L1.integral_eq_integral]
    exact integral_congr_ae ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder y x).symm
  rw [h1, ← Real.norm_eq_abs]
  refine (L1.norm_integral_le _).trans ?_
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le y x).trans ?_
  have := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖y‖ * ‖x‖ ≤ 1 * ‖y‖ * ‖x‖ := by gcongr
    _ = ‖y‖ * ‖x‖ := by rw [one_mul]

/-- **Exercise 15.5(a)**: each `f ∈ L₁(Z, 𝒵, μ)` defines a continuous linear functional
`φ(x) = ∫ f x dμ` on `L∞(Z, 𝒵, μ)`, of norm at most `‖f‖₁`. -/
theorem ex_15_5a (f : Lp ℝ 1 μ) :
    ∃ φ : StrongDual ℝ (Lp ℝ ∞ μ), (∀ x, φ x = ∫ z, f z * x z ∂μ) ∧ ‖φ‖ ≤ ‖f‖ :=
  ⟨pairL1Linf μ f, pairL1Linf_apply f, ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    fun x => by rw [Real.norm_eq_abs]; exact abs_pairL1Linf_le f x⟩

/-- **Exercise 15.5(b)**: the functional of part (a) is `x ↦ ∫ x dν` for the signed measure
`ν(A) = ∫_A f dμ`, which is absolutely continuous with respect to `μ`. The integral is Mathlib's
integral against a signed measure. The proof writes `ν = ν⁺ − ν⁻` with `ν^± = f^± μ`; this
representation step is the one the manual leaves out. -/
theorem ex_15_5b (f : Lp ℝ 1 μ) :
    ∃ ν : SignedMeasure Z, ν ≪ᵥ μ.toENNRealVectorMeasure ∧
      ∀ x : Lp ℝ ∞ μ, pairL1Linf μ f x = ∫ᵛ z, x z ∂<•ν := by
  have hfi : Integrable f μ := L1.integrable_coeFn f
  have hfm : Measurable fun z => f z := (Lp.stronglyMeasurable f).measurable
  have hfm' : Measurable fun z => -f z := hfm.neg
  set νp := μ.withDensity fun z => ENNReal.ofReal (f z)
  set νn := μ.withDensity fun z => ENNReal.ofReal (-f z)
  have : IsFiniteMeasure νp := isFiniteMeasure_withDensity_ofReal hfi.2
  have : IsFiniteMeasure νn := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  refine ⟨μ.withDensityᵥ f, Measure.withDensityᵥ_absolutelyContinuous μ f, fun x => ?_⟩
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hfi]
  have hlt : ∀ g : Z → ℝ, ∀ᵐ z ∂μ, ENNReal.ofReal (g z) < ∞ := fun g =>
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hx : MemLp (fun z => x z) ∞ μ := Lp.memLp x
  have ip : Integrable (fun z => max (f z) 0 * x z) μ := (hfi.pos_part).mul_of_top_left hx
  have ineg : Integrable (fun z => max (-f z) 0 * x z) μ := (hfi.neg.pos_part).mul_of_top_left hx
  have hp : νp.toSignedMeasure.Integrable fun z => x z := by
    simp only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    rw [integrable_withDensity_iff_integrable_smul' hfm.ennreal_ofReal (hlt _)]
    simpa [ENNReal.toReal_ofReal'] using ip
  have hn : νn.toSignedMeasure.Integrable fun z => x z := by
    simp only [VectorMeasure.Integrable, Measure.variation_toSignedMeasure]
    rw [integrable_withDensity_iff_integrable_smul' hfm'.ennreal_ofReal (hlt _)]
    simpa [ENNReal.toReal_ofReal'] using ineg
  rw [VectorMeasure.integral_sub_vectorMeasure hp hn, VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure,
    integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal (hlt _),
    integral_withDensity_eq_integral_toReal_smul hfm'.ennreal_ofReal (hlt _),
    pairL1Linf_apply]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  rw [← integral_sub ip ineg]
  congr 1
  ext z
  rw [← sub_mul, max_zero_sub_eq_self]

/-- `1_A c = c · 1_A` in `L₁`. -/
theorem indicatorConstLp_one_eq_smul {s : Set Z} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) :
    indicatorConstLp 1 hs hμs c = c • indicatorConstLp 1 hs hμs (1 : ℝ) := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := c),
    Lp.coeFn_smul c (indicatorConstLp 1 hs hμs (1 : ℝ)),
    indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with z h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  by_cases hz : z ∈ s <;> simp [hz]

/-- `∫ y (c 1_A) dμ = (∫_A y dμ) c`. -/
theorem pairLinfL1_indicator (y : Lp ℝ ∞ μ) {s : Set Z} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (c : ℝ) : pairLinfL1 μ y (indicatorConstLp 1 hs hμs c) = (∫ z in s, y z ∂μ) * c := by
  rw [pairLinfL1_apply, ← integral_mul_const, ← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hs) (hμs := hμs) (c := c)] with z hz
  rw [hz]
  by_cases h : z ∈ s <;> simp [h]

/-- For a σ-finite measure, `y ↦ (x ↦ ∫ y x dμ)` is injective from `L∞` to `L₁*`. -/
theorem pairLinfL1_injective [SigmaFinite μ] : Function.Injective (pairLinfL1 μ) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  have hint : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (fun z => y z) s μ :=
    fun s hs hμs => by
      have : Fact (μ s < ∞) := ⟨hμs⟩
      have hm : MemLp (fun z => y z) ∞ (μ.restrict s) := (Lp.memLp y).restrict s
      exact hm.integrable le_top
  have h0 := ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite hint fun s hs hμs => by
    have := pairLinfL1_indicator y hs hμs.ne 1
    rw [hy, mul_one] at this
    exact this.symm
  exact (Lp.eq_zero_iff_ae_eq_zero).2 h0

/-- For a σ-finite measure, every `φ ∈ L₁*` is `x ↦ ∫ y x dμ` for some `y ∈ L∞` with
`‖y‖∞ ≤ ‖φ‖`. Proof: take a weight `w > 0` with `∫ w dμ < ∞` and `r = √w ∈ L₂`. Then
`J x = r x` maps `L₂` into `L₁`, and Riesz representation of `φ ∘ J` gives `g ∈ L₂`. For every
measurable `s`, `|∫_s g r| ≤ ‖φ‖ ∫_s w`, so `h = g / r` has `|h| ≤ ‖φ‖` a.e. For `μ s < ∞`,
`φ(1_s) = ∫_s h`: this holds on `s ∩ {w > 1/(n+1)}` (where `1_s / r ∈ L₂`) and passes to the
limit. Indicators are dense in `L₁`. -/
theorem exists_preimage_pairLinfL1 [SigmaFinite μ] (φ : StrongDual ℝ (Lp ℝ 1 μ)) :
    ∃ y : Lp ℝ ∞ μ, pairLinfL1 μ y = φ ∧ ‖y‖ ≤ ‖φ‖ := by
  obtain ⟨w0, hw0pos, hw0m, hw0int⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  set w : Z → ℝ := fun z => (w0 z : ℝ) with hwdef
  have hwpos : ∀ z, 0 < w z := fun z => NNReal.coe_pos.2 (hw0pos z)
  have hwm : Measurable w := hw0m.coe_nnreal_real
  have hwi : Integrable w μ := by
    refine ⟨hwm.aestronglyMeasurable, ?_⟩
    simp only [HasFiniteIntegral, hwdef, Real.enorm_of_nonneg (NNReal.coe_nonneg _),
      ENNReal.ofReal_coe_nnreal]
    exact hw0int.trans ENNReal.one_lt_top
  -- the square root of the weight, an element of `L₂`
  set r : Z → ℝ := fun z => Real.sqrt (w z) with hrdef
  have hrpos : ∀ z, 0 < r z := fun z => Real.sqrt_pos.2 (hwpos z)
  have hrm : Measurable r := hwm.sqrt
  have hrr : ∀ z, r z * r z = w z := fun z => Real.mul_self_sqrt (hwpos z).le
  have hr2 : MemLp r 2 μ := by
    refine (memLp_two_iff_integrable_sq hrm.aestronglyMeasurable).2 ?_
    refine hwi.congr (Eventually.of_forall fun z => ?_)
    change w z = r z ^ 2
    rw [sq, hrr]
  set J := (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 (hr2.toLp r) with hJdef
  have hJ : ∀ (u v : Z → ℝ) (hu : MemLp u 2 μ) (hv : MemLp v 1 μ),
      (∀ z, r z * u z = v z) → J (hu.toLp u) = hv.toLp v := fun u v hu hv huv => by
    refine Lp.ext ?_
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) (hr2.toLp r)
      (hu.toLp u), hr2.coeFn_toLp, hu.coeFn_toLp, hv.coeFn_toLp] with z h1 h2 h3 h4
    change (ContinuousLinearMap.mul ℝ ℝ).holder 1 _ _ z = _
    rw [h1, ContinuousLinearMap.mul_apply', h2, h3, h4, huv]
  set g := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm (φ.comp J) with hg
  have key : ∀ (u : Z → ℝ) (hu : MemLp u 2 μ), φ (J (hu.toLp u)) = ∫ z, g z * u z ∂μ := by
    intro u hu
    have : φ (J (hu.toLp u)) = InnerProductSpace.toDual ℝ (Lp ℝ 2 μ) g (hu.toLp u) := by
      rw [hg, LinearIsometryEquiv.apply_symm_apply]; rfl
    rw [this, InnerProductSpace.toDual_apply_apply, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu.coeFn_toLp] with z hz
    rw [hz]; simp [mul_comm]
  -- `|∫_s g r| ≤ ‖φ‖ ∫_s w` for every measurable `s`
  have hgr : Integrable (fun z => g z * r z) μ := (Lp.memLp g).integrable_mul hr2
  have hwc : Integrable (fun z => ‖φ‖ * w z) μ := hwi.const_mul _
  have hset : ∀ s, MeasurableSet s → |∫ z in s, g z * r z ∂μ| ≤ ∫ z in s, ‖φ‖ * w z ∂μ := by
    intro s hs
    have hu : MemLp (s.indicator r) 2 μ := hr2.indicator hs
    have hv : MemLp (s.indicator w) 1 μ := (memLp_one_iff_integrable.2 hwi).indicator hs
    have huv : ∀ z, r z * s.indicator r z = s.indicator w z := fun z => by
      by_cases hz : z ∈ s <;> simp [hz, hrr]
    have e1 : φ (hv.toLp _) = ∫ z in s, g z * r z ∂μ := by
      rw [← hJ _ _ hu hv huv, key, ← integral_indicator hs]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ s <;> simp [hz]
    have e2 : ‖hv.toLp (s.indicator w)‖ = ∫ z in s, w z ∂μ := by
      rw [L1.norm_eq_integral_norm, ← integral_indicator hs]
      refine integral_congr_ae ?_
      filter_upwards [hv.coeFn_toLp] with z hz
      rw [hz]
      by_cases hzs : z ∈ s <;> simp [hzs, abs_of_pos (hwpos z)]
    rw [← e1, integral_const_mul, ← e2, ← Real.norm_eq_abs]
    exact φ.le_opNorm _
  have hle : (fun z => g z * r z) ≤ᵐ[μ] fun z => ‖φ‖ * w z :=
    ae_le_of_forall_setIntegral_le hgr hwc fun s hs _ => (le_abs_self _).trans (hset s hs)
  have hge : (fun z => -(‖φ‖ * w z)) ≤ᵐ[μ] fun z => g z * r z :=
    ae_le_of_forall_setIntegral_le hwc.neg hgr fun s hs _ => by
      rw [integral_neg]; linarith [neg_abs_le (∫ z in s, g z * r z ∂μ), hset s hs]
  set h : Z → ℝ := fun z => g z / r z with hhdef
  have hb : ∀ᵐ z ∂μ, ‖h z‖ ≤ ‖φ‖ := by
    filter_upwards [hle, hge] with z h1 h2
    have hr := hrpos z
    rw [Real.norm_eq_abs, hhdef, abs_div, abs_of_pos hr, div_le_iff₀ hr]
    have h4 : |g z * r z| ≤ ‖φ‖ * w z := abs_le.2 ⟨h2, h1⟩
    rw [abs_mul, abs_of_pos hr, ← hrr, ← mul_assoc] at h4
    exact le_of_mul_le_mul_right h4 hr
  have hhm : AEStronglyMeasurable h μ :=
    ((Lp.aestronglyMeasurable g).aemeasurable.div hrm.aemeasurable).aestronglyMeasurable
  have hm : MemLp h ∞ μ := memLp_top_of_bound hhm ‖φ‖ hb
  -- `φ(1_s) = ∫_s h` for `μ s < ∞`, by exhausting `s` with `tₙ = s ∩ {w > 1/(n+1)}`
  have hind : ∀ s (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      φ (indicatorConstLp 1 hs hμs (1 : ℝ)) = ∫ z in s, h z ∂μ := by
    intro s hs hμs
    set t : ℕ → Set Z := fun n => s ∩ {z | 1 / ((n : ℝ) + 1) < w z} with htdef
    have ht : ∀ n, MeasurableSet (t n) := fun n =>
      hs.inter (measurableSet_lt measurable_const hwm)
    have hμt : ∀ n, μ (t n) ≠ ∞ := fun n =>
      ne_top_of_le_ne_top hμs (measure_mono inter_subset_left)
    have hmono : Monotone t := fun m n hmn z hz => by
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have h2 : 1 / ((m : ℝ) + 1) < w z := hz.2
      exact ⟨hz.1, lt_of_le_of_lt (by gcongr) h2⟩
    have hunion : (⋃ n, t n) = s := by
      refine Subset.antisymm (iUnion_subset fun n => inter_subset_left) fun z hz => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hwpos z)
      exact mem_iUnion.2 ⟨n, hz, hn⟩
    have hval : ∀ n, φ (indicatorConstLp 1 (ht n) (hμt n) (1 : ℝ)) = ∫ z in t n, h z ∂μ := by
      intro n
      have hcm : MemLp ((t n).indicator fun _ => Real.sqrt ((n : ℝ) + 1)) 2 μ :=
        memLp_indicator_const 2 (ht n) _ (Or.inr (hμt n))
      have hu : MemLp ((t n).indicator fun z => 1 / r z) 2 μ := by
        refine hcm.of_le (((hrm.const_div 1).indicator (ht n)).aestronglyMeasurable)
          (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ t n
        · have hr := hrpos z
          simp only [indicator_of_mem hz, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 hr),
            abs_of_nonneg (Real.sqrt_nonneg _)]
          rw [div_le_iff₀ hr]
          have h1 : 1 ≤ ((n : ℝ) + 1) * w z := by
            have h2 : 1 / ((n : ℝ) + 1) < w z := hz.2
            rw [div_lt_iff₀ (by positivity)] at h2
            linarith
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ ≤ Real.sqrt (((n : ℝ) + 1) * w z) := Real.sqrt_le_sqrt h1
            _ = Real.sqrt ((n : ℝ) + 1) * r z := Real.sqrt_mul (by positivity) _
        · simp [indicator_of_notMem hz]
      have huv : ∀ z, r z * (t n).indicator (fun z => 1 / r z) z = (t n).indicator (fun _ => 1) z :=
        fun z => by
          by_cases hz : z ∈ t n
          · simp [hz, (hrpos z).ne']
          · simp [hz]
      have := hJ _ _ hu (memLp_indicator_const 1 (ht n) (1 : ℝ) (Or.inr (hμt n))) huv
      change φ (MemLp.toLp _ (memLp_indicator_const 1 (ht n) (1 : ℝ) (Or.inr (hμt n)))) = _
      rw [← this, key, ← integral_indicator (ht n)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ t n
      · simp [hz, hhdef, div_eq_mul_inv]
      · simp [hz]
    have hsd : Tendsto (fun n => μ (t n ∆ s)) atTop (𝓝 0) := by
      have e : ∀ n, t n ∆ s = s \ t n := fun n => symmDiff_of_le inter_subset_left
      simp only [e]
      have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := fun n => s \ t n)
        (fun n => (hs.diff (ht n)).nullMeasurableSet)
        (fun m n hmn z hz => ⟨hz.1, fun h' => hz.2 (hmono hmn h')⟩)
        ⟨0, ne_top_of_le_ne_top hμs (measure_mono sdiff_subset)⟩
      have hempty : (⋂ n, s \ t n) = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
        have hzs : z ∈ s := (mem_iInter.1 hz 0).1
        rw [← hunion] at hzs
        obtain ⟨n, hn⟩ := mem_iUnion.1 hzs
        exact (mem_iInter.1 hz n).2 hn
      rw [hempty, measure_empty] at hlim
      exact hlim
    have h1 := (φ.continuous.tendsto _).comp
      (tendsto_indicatorConstLp_set (hs := hs) (hμs := hμs) (c := (1 : ℝ)) (ht := ht)
        (hμt := hμt) ENNReal.one_ne_top hsd)
    have hio : IntegrableOn h (⋃ n, t n) μ := by
      rw [hunion]
      have : Fact (μ s < ∞) := ⟨hμs.lt_top⟩
      exact (hm.restrict s).integrable le_top
    have h2 := tendsto_setIntegral_of_monotone ht hmono hio
    rw [hunion] at h2
    exact tendsto_nhds_unique h1 (h2.congr fun n => (hval n).symm)
  refine ⟨hm.toLp h, ?_, ?_⟩
  · refine (Lp.induction (p := 1) ENNReal.one_ne_top
      (fun x => pairLinfL1 μ (hm.toLp h) x = φ x) ?_ ?_
      (isClosed_eq (pairLinfL1 μ (hm.toLp h)).continuous φ.continuous) ·) |>
      ContinuousLinearMap.ext
    · intro c s hs hμs
      rw [Lp.simpleFunc.coe_indicatorConst, pairLinfL1_indicator, indicatorConstLp_one_eq_smul,
        map_smul, smul_eq_mul, hind s hs hμs.ne, mul_comm]
      congr 1
      exact setIntegral_congr_ae hs (by
        filter_upwards [hm.coeFn_toLp] with z hz _ using hz)
    · intro f f' hf hf' _ h1 h2
      simp only [map_add, h1, h2]
  · rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
    refine ENNReal.toReal_le_of_le_ofReal (norm_nonneg φ) (eLpNormEssSup_le_of_ae_bound ?_)
    filter_upwards [hm.coeFn_toLp, hb] with z h1 h2
    rw [h1]; exact h2

/-- For a σ-finite measure, `y ↦ (x ↦ ∫ y x dμ)` preserves norms from `L∞` to `L₁*`. -/
theorem norm_pairLinfL1 [SigmaFinite μ] (y : Lp ℝ ∞ μ) : ‖pairLinfL1 μ y‖ = ‖y‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
      rw [Real.norm_eq_abs]; exact abs_pairLinfL1_le y x
  · obtain ⟨y', hy', hn⟩ := exists_preimage_pairLinfL1 (pairLinfL1 μ y)
    calc ‖y‖ = ‖y'‖ := by rw [pairLinfL1_injective hy']
      _ ≤ ‖pairLinfL1 μ y‖ := hn

/-- `L₁* = L∞` for a σ-finite measure. -/
noncomputable def dualL1 (μ : Measure Z) [SigmaFinite μ] :
    Lp ℝ ∞ μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ 1 μ) :=
  LinearIsometryEquiv.ofSurjective ⟨(pairLinfL1 μ).toLinearMap, norm_pairLinfL1⟩
    fun φ => (exists_preimage_pairLinfL1 φ).imp fun _ h => h.1

/-- **Corrected `L₁* = L∞`** (p. 449): for a σ-finite measure, every `y ∈ L∞` gives
`x ↦ ∫ y x dμ` in `L₁*`, every element of `L₁*` arises from exactly one `y`, and norms are
preserved. -/
theorem l1_dual_sigmaFinite [SigmaFinite μ] :
    ∃ e : Lp ℝ ∞ μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ 1 μ), ∀ y x, e y x = ∫ z, y z * x z ∂μ :=
  ⟨dualL1 μ, fun y x => pairLinfL1_apply y x⟩

/-- One point of infinite mass: the measure `∞ · δ` on `Unit`. It is not σ-finite. -/
noncomputable def infAtom : Measure Unit := (∞ : ℝ≥0∞) • Measure.dirac ()

/-- For `infAtom`, `L₁ = {0}`: an integrable function must vanish at the atom. -/
theorem subsingleton_L1_infAtom : Subsingleton (Lp ℝ 1 infAtom) := by
  refine ⟨fun f g => ?_⟩
  have h0 : ∀ h : Lp ℝ 1 infAtom, h = 0 := fun h => by
    have hi : Integrable h infAtom := L1.integrable_coeFn h
    have hlt := hi.2
    change ∫⁻ a, ‖h a‖ₑ ∂((∞ : ℝ≥0∞) • Measure.dirac ()) < ∞ at hlt
    rw [lintegral_smul_measure, lintegral_dirac] at hlt
    have hz : ‖h ()‖ₑ = 0 := by
      by_contra hne
      exact (ENNReal.mul_lt_top_iff.1 hlt).elim (fun h' => absurd h'.1 (lt_irrefl _))
        (fun h' => h'.elim (fun h'' => absurd h'' (by simp)) hne)
    rw [Lp.eq_zero_iff_ae_eq_zero]
    refine Eventually.of_forall fun u => ?_
    cases u
    simpa using hz
  rw [h0 f, h0 g]

/-- For `infAtom`, `L∞ ≠ {0}`: the constant `1` is not `0`. -/
theorem nontrivial_Linf_infAtom : Nontrivial (Lp ℝ ∞ infAtom) := by
  refine ⟨⟨(memLp_top_const (μ := infAtom) (1 : ℝ)).toLp _, 0, fun h => ?_⟩⟩
  have := (MemLp.toLp_eq_toLp_iff _ (memLp_top_const (μ := infAtom) (0 : ℝ))).1
    (h.trans (MemLp.toLp_zero _).symm)
  rw [EventuallyEq, ae_iff] at this
  simp [infAtom] at this

/-- **Correction (p. 449)**: without σ-finiteness the dual of `L₁` is not `L∞`. For `infAtom`
there is no linear isomorphism `L∞ ≃ L₁*` at all. -/
theorem l1_dual_counterexample :
    IsEmpty (Lp ℝ ∞ infAtom ≃ₗ[ℝ] StrongDual ℝ (Lp ℝ 1 infAtom)) := by
  refine ⟨fun e => ?_⟩
  have h1 := subsingleton_L1_infAtom
  have hd : Subsingleton (StrongDual ℝ (Lp ℝ 1 infAtom)) :=
    ⟨fun φ ψ => ContinuousLinearMap.ext fun x => by
      rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  have h2 := nontrivial_Linf_infAtom
  obtain ⟨a, b, hab⟩ := h2.exists_pair_ne
  exact hab (e.injective (Subsingleton.elim _ _))

/-- **Correction (p. 449)**: for `infAtom` the map `y ↦ (x ↦ ∫ y x dμ)` from `L∞` to `L₁*` is
not injective. -/
theorem l1_dual_pairing_counterexample : ¬ Function.Injective (pairLinfL1 infAtom) := by
  intro hinj
  have h1 := subsingleton_L1_infAtom
  obtain ⟨a, b, hab⟩ := nontrivial_Linf_infAtom.exists_pair_ne
  refine hab (hinj (ContinuousLinearMap.ext fun x => ?_))
  rw [Subsingleton.elim x 0, map_zero, map_zero]

/-- **Correction (p. 450)**: no measure has `μ(A) > 0` for every measurable `A`, since
`μ(∅) = 0`. -/
theorem positive_measure_counterexample (μ : Measure Z) : ¬ ∀ A : Set Z, 0 < μ A :=
  fun h => by simpa using h ∅

/-! ### The example on p. 450: `L∞(ℕ, μ) = ℓ∞` -/

variable {ν : Measure ℕ}

/-- If every point has positive mass, an a.e. property holds everywhere. -/
theorem of_ae_of_atoms_pos (hν : ∀ n, ν {n} ≠ 0) {P : ℕ → Prop} (h : ∀ᵐ n ∂ν, P n) (m : ℕ) :
    P m := by
  by_contra hm
  rw [ae_iff] at h
  exact hν m (measure_mono_null (fun n hn => by rw [mem_singleton_iff.1 hn]; exact hm) h)

/-- An element of `L∞` is bounded a.e. by its norm. -/
theorem ae_norm_le_norm_Linf (f : Lp ℝ ∞ ν) : ∀ᵐ n ∂ν, ‖f n‖ ≤ ‖f‖ := by
  have h := ae_le_eLpNormEssSup (f := fun n => f n) (μ := ν)
  have hfin : eLpNormEssSup (fun n => f n) ν ≠ ∞ := by
    have := Lp.eLpNorm_ne_top f
    rwa [eLpNorm_exponent_top (Lp.aestronglyMeasurable f)] at this
  filter_upwards [h] with n hn
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
  rw [← ofReal_norm] at hn
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hn

/-- A bounded sequence is an element of `L∞(ℕ, ν)`. -/
theorem memLp_ellInfSp (x : ellInfSp) : MemLp (fun n => x n) ∞ ν :=
  memLp_top_of_bound Measurable.of_discrete.aestronglyMeasurable ‖x‖
    (Eventually.of_forall fun n => lp.norm_apply_le_norm (by simp) x n)

/-- The map `ℓ∞ → L∞(ℕ, ν)` sending a bounded sequence to its class. -/
noncomputable def ellInfToLinf (ν : Measure ℕ) : ellInfSp →ₗ[ℝ] Lp ℝ ∞ ν where
  toFun x := (memLp_ellInfSp x).toLp _
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' _ _ := MemLp.toLp_const_smul _ _

/-- The class of `x` is represented by `x`. -/
theorem coeFn_ellInfToLinf (x : ellInfSp) : ellInfToLinf ν x =ᵐ[ν] fun n => x n :=
  (memLp_ellInfSp x).coeFn_toLp

/-- If every point has positive mass, `ℓ∞ → L∞(ℕ, ν)` preserves norms. -/
theorem norm_ellInfToLinf [IsFiniteMeasure ν] (hν : ∀ n, ν {n} ≠ 0) (x : ellInfSp) :
    ‖ellInfToLinf ν x‖ = ‖x‖ := by
  apply le_antisymm
  · have := Lp.norm_le_of_ae_bound (p := ∞) (f := ellInfToLinf ν x) (norm_nonneg x) (by
      filter_upwards [coeFn_ellInfToLinf (ν := ν) x] with n h
      rw [h]; exact lp.norm_apply_le_norm (by simp) x n)
    simpa using this
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun n => ?_
    obtain ⟨h3, h4⟩ := of_ae_of_atoms_pos hν
      ((ae_norm_le_norm_Linf (ellInfToLinf ν x)).and (coeFn_ellInfToLinf (ν := ν) x)) n
    rw [h4] at h3
    exact h3

/-- If every point has positive mass, every class in `L∞(ℕ, ν)` comes from a bounded
sequence. -/
theorem ellInfToLinf_surjective (hν : ∀ n, ν {n} ≠ 0) :
    Function.Surjective (ellInfToLinf ν) := by
  intro f
  let x : ellInfSp := ⟨fun n => f n, memℓp_infty_iff.2 ⟨‖f‖, by
    rintro _ ⟨n, rfl⟩
    exact of_ae_of_atoms_pos hν (ae_norm_le_norm_Linf f) n⟩⟩
  refine ⟨x, Lp.ext ?_⟩
  filter_upwards [coeFn_ellInfToLinf (ν := ν) x] with n hn
  exact hn

/-- **Example (p. 450)**, with the typo corrected: if `ν` is a finite measure on `ℕ` (all
subsets measurable) with `ν {n} > 0` for every `n`, then `L∞(ℕ, ν)` is `ℓ∞`. The isometric
isomorphism sends a bounded sequence to its class. -/
theorem example_15_4_linf_nat [IsFiniteMeasure ν] (hν : ∀ n, ν {n} ≠ 0) :
    ∃ e : ellInfSp ≃ₗᵢ[ℝ] Lp ℝ ∞ ν, ∀ x, e x =ᵐ[ν] fun n => x n :=
  ⟨LinearIsometryEquiv.ofSurjective ⟨ellInfToLinf ν, norm_ellInfToLinf hν⟩
    (ellInfToLinf_surjective hν), fun x => coeFn_ellInfToLinf x⟩

/-! ### Theorem 15.2: the geometric Hahn–Banach theorem -/

/-- If `φ(b) ≤ φ(a)` for all `a ∈ A`, `b ∈ B` (both nonempty), a constant `c` fits between:
`φ(b) ≤ c ≤ φ(a)`. -/
theorem exists_const_between_of_le {A B : Set S} (hA : A.Nonempty) (hB : B.Nonempty)
    (φ : StrongDual ℝ S) (h : ∀ x ∈ A, ∀ y ∈ B, φ y ≤ φ x) :
    ∃ c : ℝ, (∀ x ∈ A, c ≤ φ x) ∧ ∀ y ∈ B, φ y ≤ c := by
  obtain ⟨a, ha⟩ := hA
  have hbdd : BddAbove (φ '' B) := ⟨φ a, by rintro _ ⟨y, hy, rfl⟩; exact h a ha y hy⟩
  refine ⟨sSup (φ '' B), fun x hx => csSup_le (hB.image _) ?_, fun y hy =>
    le_csSup hbdd (mem_image_of_mem _ hy)⟩
  rintro _ ⟨y, hy, rfl⟩
  exact h x hx y hy

/-- **Theorem 15.2, interior-point case**: if `A, B` are convex, `A ≠ ∅`, `B̊ ≠ ∅` and
`A ∩ B̊ = ∅`, then some nonzero `φ ∈ S*` and `c` satisfy `φ(y) ≤ c ≤ φ(x)` for `x ∈ A`,
`y ∈ B`. This is Mathlib's `geometric_hahn_banach_of_nonempty_interior`. -/
theorem theorem_15_2_interior {A B : Set S} (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hAne : A.Nonempty) (hBint : (interior B).Nonempty) (hAB : A ∩ interior B = ∅) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ A, c ≤ φ x) ∧ ∀ y ∈ B, φ y ≤ c := by
  obtain ⟨f, u, hf, hB', hA'⟩ := geometric_hahn_banach_of_nonempty_interior hB hA
    (Set.disjoint_iff_inter_eq_empty.2 (by rw [inter_comm]; exact hAB)) hBint hAne
  exact ⟨f, hf, u, hA', hB'⟩

/-- **Theorem 15.2, finite-dimensional case**: in a finite-dimensional space, disjoint nonempty
convex sets are separated by a nonzero functional. Proof with `C = A − B` (convex, `0 ∉ C`): if
`C̊ ≠ ∅`, separate `0` from `C` with the interior-point case. Otherwise the affine span of `C` is
a proper affine subspace, and a nonzero functional vanishing on its direction is constant
on `C`. -/
theorem theorem_15_2_finiteDimensional [FiniteDimensional ℝ S] {A B : Set S} (hA : Convex ℝ A)
    (hB : Convex ℝ B) (hAne : A.Nonempty) (hBne : B.Nonempty) (hAB : A ∩ B = ∅) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ A, c ≤ φ x) ∧ ∀ y ∈ B, φ y ≤ c := by
  suffices h : ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∀ x ∈ A, ∀ y ∈ B, φ y ≤ φ x by
    obtain ⟨φ, hφ, h⟩ := h
    exact ⟨φ, hφ, exists_const_between_of_le hAne hBne φ h⟩
  have hC : Convex ℝ (A - B) := hA.sub hB
  have h0 : (0 : S) ∉ A - B := by
    rintro ⟨a, ha, b, hb, hab⟩
    have : a = b := sub_eq_zero.1 hab
    exact (Set.eq_empty_iff_forall_notMem.1 hAB) a ⟨ha, this ▸ hb⟩
  by_cases hint : (interior (A - B)).Nonempty
  · obtain ⟨f, u, hf, hC', h0'⟩ := geometric_hahn_banach_of_nonempty_interior hC
      (convex_singleton 0) (disjoint_singleton_right.2 fun h => h0 (interior_subset h)) hint
      (singleton_nonempty 0)
    refine ⟨-f, neg_ne_zero.2 hf, fun x hx y hy => ?_⟩
    have h1 := hC' (x - y) (sub_mem_sub hx hy)
    have h2 := h0' 0 rfl
    simp only [map_zero, map_sub] at h1 h2
    simp only [neg_apply]
    linarith
  · have hspan : affineSpan ℝ (A - B) ≠ ⊤ := fun h =>
      hint (hC.interior_nonempty_iff_affineSpan_eq_top.2 h)
    obtain ⟨a0, ha0⟩ := hAne
    obtain ⟨b0, hb0⟩ := hBne
    have hc0 : a0 - b0 ∈ A - B := sub_mem_sub ha0 hb0
    have hdir : (affineSpan ℝ (A - B)).direction < ⊤ := by
      refine lt_top_iff_ne_top.2 fun h => hspan ?_
      exact (AffineSubspace.direction_eq_top_iff_of_nonempty
        ((affineSpan_nonempty ℝ).2 ⟨_, hc0⟩)).1 h
    obtain ⟨f, hf0, hker⟩ := Submodule.exists_le_ker_of_lt_top _ hdir
    let g : StrongDual ℝ S := LinearMap.toContinuousLinearMap f
    have hg0 : g ≠ 0 := fun h => hf0 (LinearMap.ext fun x => congrArg (fun φ => φ x) h)
    have hconst : ∀ x ∈ A, ∀ y ∈ B, g (x - y) = g (a0 - b0) := fun x hx y hy => by
      have hm : (x - y) -ᵥ (a0 - b0) ∈ (affineSpan ℝ (A - B)).direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan _ _ (sub_mem_sub hx hy))
          (subset_affineSpan _ _ hc0)
      have := hker hm
      rw [LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero] at this
      exact this
    by_cases hk : 0 ≤ g (a0 - b0)
    · refine ⟨g, hg0, fun x hx y hy => ?_⟩
      have := hconst x hx y hy
      rw [map_sub] at this
      linarith
    · refine ⟨-g, neg_ne_zero.2 hg0, fun x hx y hy => ?_⟩
      have := hconst x hx y hy
      rw [map_sub] at this
      simp only [neg_apply]
      linarith

/-- **Theorem 15.2** (corrected, with `A ≠ ∅` and, in the finite-dimensional case, `B ≠ ∅`):
for convex `A, B ⊆ S` with either `B̊ ≠ ∅` and `A ∩ B̊ = ∅`, or `S` finite dimensional and
`A ∩ B = ∅`, some nonzero `φ ∈ S*` and `c ∈ ℝ` satisfy `φ(y) ≤ c ≤ φ(x)` for all `x ∈ A`,
`y ∈ B`. -/
theorem theorem_15_2 {A B : Set S} (hA : Convex ℝ A) (hB : Convex ℝ B) (hAne : A.Nonempty)
    (h : ((interior B).Nonempty ∧ A ∩ interior B = ∅) ∨
      (FiniteDimensional ℝ S ∧ B.Nonempty ∧ A ∩ B = ∅)) :
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ A, c ≤ φ x) ∧ ∀ y ∈ B, φ y ≤ c := by
  rcases h with ⟨hBint, hAB⟩ | ⟨hfin, hBne, hAB⟩
  · exact theorem_15_2_interior hA hB hAne hBint hAB
  · exact theorem_15_2_finiteDimensional hA hB hAne hBne hAB

/-- The book's statement of Theorem 15.2 (pp. 450–451), with no nonemptiness hypotheses. -/
def BookTheorem15_2 (S : Type*) [NormedAddCommGroup S] [NormedSpace ℝ S] : Prop :=
  ∀ A B : Set S, Convex ℝ A → Convex ℝ B →
    (((interior B).Nonempty ∧ A ∩ interior B = ∅) ∨ (FiniteDimensional ℝ S ∧ A ∩ B = ∅)) →
    ∃ φ : StrongDual ℝ S, φ ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ A, c ≤ φ x) ∧ ∀ y ∈ B, φ y ≤ c

/-- A nonzero continuous linear functional is unbounded above. -/
theorem exists_lt_apply_of_ne_zero {φ : StrongDual ℝ S} (hφ : φ ≠ 0) (c : ℝ) :
    ∃ y, c < φ y := by
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h
    exact hφ (ContinuousLinearMap.ext fun v => not_not.1 fun hv => h ⟨v, hv⟩)
  refine ⟨((|c| + 1) / φ v) • v, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  linarith [le_abs_self c]

/-- **Correction (p. 450)**: the book's Theorem 15.2 is false on `ℝ`. Take `A = ∅` and `B = ℝ`:
`B` has interior points and `A ∩ B̊ = ∅`, but no nonzero `φ` is bounded above on `B`. -/
theorem theorem_15_2_counterexample : ¬ BookTheorem15_2 ℝ := by
  intro h
  obtain ⟨φ, hφ, c, -, hB⟩ := h ∅ univ convex_empty convex_univ
    (Or.inl ⟨by simp, by simp⟩)
  obtain ⟨y, hy⟩ := exists_lt_apply_of_ne_zero hφ c
  exact absurd (hB y trivial) (not_le.2 hy)

/-- **Correction (p. 450)**, finite-dimensional case: `A = ℝ`, `B = ∅` satisfy the book's
hypotheses (`ℝ` is finite dimensional and `A ∩ B = ∅`), but no nonzero `φ` is bounded below
on `A`. -/
theorem theorem_15_2_counterexample_finiteDimensional :
    FiniteDimensional ℝ ℝ ∧ (univ : Set ℝ) ∩ ∅ = ∅ ∧
      ¬ ∃ φ : StrongDual ℝ ℝ, φ ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ (univ : Set ℝ), c ≤ φ x) ∧
        ∀ y ∈ (∅ : Set ℝ), φ y ≤ c := by
  refine ⟨inferInstance, by simp, ?_⟩
  rintro ⟨φ, hφ, c, hA, -⟩
  obtain ⟨y, hy⟩ := exists_lt_apply_of_ne_zero (neg_ne_zero.2 hφ) (-c)
  have := hA y trivial
  simp only [neg_apply] at hy
  linarith

/-! ### Exercise 15.6 -/

variable {β : ℝ}

/-- **Exercise 15.6** (book form): for `0 < β < 1` and every `ε > 0` there is a sequence `y`
with `Σ βᵗ |yₜ| < ε` and some `|yₜ| > 1`. So every ball about `θ` in
`S = {x : Σ βᵗ |xₜ| < ∞}` leaves `B = {x : |xₜ| ≤ 1 for all t}`, and `θ ∉ B̊`. The book's
witness has one entry `ε/β^{T−1}`; here it is `2` at a `T` with `βᵀ < ε/2`. -/
theorem ex_15_6 (hβ0 : 0 < β) (hβ1 : β < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℕ → ℝ, Summable (fun t => β ^ t * |y t|) ∧ ∑' t, β ^ t * |y t| < ε ∧
      ¬ ∀ t, |y t| ≤ 1 := by
  obtain ⟨T, hT⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).eventually
    (gt_mem_nhds (half_pos hε))).exists
  have hs : ∀ t, t ≠ T → β ^ t * |(Pi.single T (2 : ℝ) : ℕ → ℝ) t| = 0 := fun t ht => by
    simp [Pi.single_eq_of_ne ht]
  refine ⟨Pi.single T 2, summable_of_ne_finset_zero (s := {T}) fun t ht =>
    hs t (by simpa using ht), ?_, fun h => ?_⟩
  · rw [tsum_eq_single T hs, Pi.single_eq_same]
    norm_num
    linarith
  · have := h T
    rw [Pi.single_eq_same] at this
    norm_num at this

/-- The isometry from the book's space `S = {x : Σ βᵗ |xₜ| < ∞}` onto `ℓ₁`, `xₜ ↦ βᵗ xₜ`. -/
noncomputable def weightToEllOne (β : ℝ) (x : ℕ → ℝ) (hx : Summable fun t => β ^ t * |x t|)
    (hβ : 0 ≤ β) : ellOneSp :=
  ⟨fun t => β ^ t * x t, (memℓp_gen_iff (p := 1) (by simp)).2 (by
    refine hx.congr fun t => ?_
    simp [abs_of_nonneg hβ])⟩

/-- `weightToEllOne` is an isometry: `‖x − x'‖_S = Σ βᵗ |xₜ − x'ₜ|` is the `ℓ₁` distance of
the images. -/
theorem dist_weightToEllOne (hβ : 0 ≤ β) {x x' : ℕ → ℝ} (hx : Summable fun t => β ^ t * |x t|)
    (hx' : Summable fun t => β ^ t * |x' t|) :
    dist (weightToEllOne β x hx hβ) (weightToEllOne β x' hx' hβ) =
      ∑' t, β ^ t * |x t - x' t| := by
  rw [dist_eq_norm, lp.norm_eq_tsum_rpow (by simp)]
  simp only [ENNReal.toReal_one, Real.rpow_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]
  congr 1
  ext t
  change ‖β ^ t * x t - β ^ t * x' t‖ = _
  rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hβ t)]

/-- `weightToEllOne` maps the book's space `S` onto `ℓ₁`. -/
theorem weightToEllOne_surjective (hβ : 0 < β) (z : ellOneSp) :
    ∃ x : ℕ → ℝ, ∃ hx : Summable (fun t => β ^ t * |x t|), weightToEllOne β x hx hβ.le = z := by
  refine ⟨fun t => z t / β ^ t, (summable_abs_ellOneSp z).congr fun t => ?_, ?_⟩
  · rw [abs_div, abs_of_pos (pow_pos hβ t), mul_div_cancel₀ _ (pow_pos hβ t).ne']
  · refine lp.ext (funext fun t => ?_)
    change β ^ t * (z t / β ^ t) = z t
    rw [mul_div_cancel₀ _ (pow_pos hβ t).ne']

/-- The image of the box `B = {|xₜ| ≤ 1}` under `weightToEllOne`: `{z ∈ ℓ₁ : |zₜ| ≤ βᵗ}`. -/
def ex156Box (β : ℝ) : Set ellOneSp := {z | ∀ t, |z t| ≤ β ^ t}

/-- `weightToEllOne` maps `B` exactly onto `ex156Box β`. -/
theorem weightToEllOne_mem_ex156Box_iff (hβ : 0 < β) {x : ℕ → ℝ}
    (hx : Summable fun t => β ^ t * |x t|) :
    weightToEllOne β x hx hβ.le ∈ ex156Box β ↔ ∀ t, |x t| ≤ 1 := by
  refine forall_congr' fun t => ?_
  change |β ^ t * x t| ≤ β ^ t ↔ _
  rw [abs_mul, abs_of_pos (pow_pos hβ t)]
  constructor
  · intro h; exact le_of_mul_le_mul_left (by simpa using h) (pow_pos hβ t)
  · intro h; exact mul_le_of_le_one_right (pow_pos hβ t).le h

/-- The box is convex. -/
theorem convex_ex156Box : Convex ℝ (ex156Box β) := by
  intro x hx y hy a b ha hb hab t
  change |a * x t + b * y t| ≤ β ^ t
  calc |a * x t + b * y t| ≤ a * |x t| + b * |y t| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * β ^ t + b * β ^ t := by gcongr; exacts [hx t, hy t]
    _ = β ^ t := by rw [← add_mul, hab, one_mul]

/-- `θ` lies in the box. -/
theorem zero_mem_ex156Box (hβ : 0 < β) : (0 : ellOneSp) ∈ ex156Box β := fun t => by
  simp [(pow_pos hβ t).le]

/-- The box has empty interior: from any `z` in it, `z + 3βᵗ eₜ` is within `3βᵗ` but outside
it. -/
theorem interior_ex156Box (hβ0 : 0 < β) (hβ1 : β < 1) : interior (ex156Box β) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hz)
  have hzB : z ∈ ex156Box β := interior_subset hz
  obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).eventually
    (gt_mem_nhds (div_pos hε three_pos))).exists
  have hw : z + lp.single 1 t (3 * β ^ t) ∈ ball z ε := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, lp.norm_single (by simp), Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  have h1 := hball hw t
  have h2 := hzB t
  change |z t + (Pi.single t (3 * β ^ t) : ℕ → ℝ) t| ≤ β ^ t at h1
  rw [Pi.single_eq_same] at h1
  have hp := pow_pos hβ0 t
  have := neg_abs_le (z t)
  have := abs_le.1 h1
  have := abs_le.1 h2
  linarith

/-- **Exercise 15.6** (in `ℓ₁` coordinates): `θ` is not an interior point of `B`. -/
theorem ex_15_6_zero_notMem_interior (hβ0 : 0 < β) (hβ1 : β < 1) :
    (0 : ellOneSp) ∉ interior (ex156Box β) := by
  rw [interior_ex156Box hβ0 hβ1]; exact notMem_empty _

/-- The only continuous linear `φ` with `φ ≤ 0` on `B` is `φ = 0` (the book's claim on p. 451):
`B = −B`, `βᵗ eₜ ∈ B`, and the `eₜ` determine `φ`. -/
theorem eq_zero_of_le_zero_on_ex156Box (hβ0 : 0 < β) {φ : StrongDual ℝ ellOneSp}
    (h : ∀ z ∈ ex156Box β, φ z ≤ 0) : φ = 0 := by
  have hs : ∀ t, φ (lp.single 1 t 1) = 0 := fun t => by
    have hp := pow_pos hβ0 t
    have mem : ∀ a : ℝ, |a| ≤ 1 → lp.single 1 t (a * β ^ t) ∈ ex156Box β := fun a ha s => by
      change |(Pi.single t (a * β ^ t) : ℕ → ℝ) s| ≤ β ^ s
      by_cases hst : s = t
      · subst hst
        rw [Pi.single_eq_same, abs_mul, abs_of_pos hp]
        exact mul_le_of_le_one_left hp.le ha
      · rw [Pi.single_eq_of_ne hst]; simp [(pow_pos hβ0 s).le]
    have e : ∀ a : ℝ, φ (lp.single 1 t (a * β ^ t)) = a * β ^ t * φ (lp.single 1 t 1) :=
      fun a => by
        have hsm : lp.single 1 t (a * β ^ t) =
            (a * β ^ t) • lp.single (E := fun _ : ℕ => ℝ) 1 t 1 := by
          rw [← lp.single_smul, smul_eq_mul, mul_one]
        rw [hsm, map_smul, smul_eq_mul]
    have h1 := h _ (mem 1 (by simp))
    have h2 := h _ (mem (-1) (by simp))
    rw [e] at h1 h2
    have : β ^ t * φ (lp.single 1 t 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hp.ne'
    · exact h
  refine lp.ext_continuousLinearMap (by simp) fun t => ?_
  ext
  simp [hs t]

/-- Without an interior point Theorem 15.2 fails (p. 451): `A = {θ}` and `B` are convex and
`A ∩ B̊ = ∅`, but no nonzero `φ` and `c` give `φ(y) ≤ c ≤ φ(x)` on `B` and `A`. -/
theorem ex_15_6_no_separation (hβ0 : 0 < β) (hβ1 : β < 1) :
    Convex ℝ ({0} : Set ellOneSp) ∧ Convex ℝ (ex156Box β) ∧
      ({0} : Set ellOneSp) ∩ interior (ex156Box β) = ∅ ∧
      ¬ ∃ φ : StrongDual ℝ ellOneSp, φ ≠ 0 ∧ ∃ c : ℝ, (∀ x ∈ ({0} : Set ellOneSp), c ≤ φ x) ∧
        ∀ y ∈ ex156Box β, φ y ≤ c := by
  refine ⟨convex_singleton 0, convex_ex156Box, by simp [interior_ex156Box hβ0 hβ1], ?_⟩
  rintro ⟨φ, hφ, c, hA, hB⟩
  have hc : c ≤ 0 := by simpa using hA 0 rfl
  exact hφ (eq_zero_of_le_zero_on_ex156Box hβ0 fun z hz => (hB z hz).trans hc)

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The dual of `L_p` for `1 < p < ∞`

SLP §15.1, Example 4, pp. 448–450: for `1 ≤ p < ∞` and `1/p + 1/q = 1` the dual of
`L_p(Z, 𝒵, μ)` is `L_q(Z, 𝒵, μ)`. The book states this without proof. The case `p = 1` (with
σ-finiteness) is `l1_dual_sigmaFinite` in `DualSpaces`. Here `1 < p < ∞` and `μ` is a finite
measure, which covers the probability spaces the book uses.

* **Example 4** (`example_15_4`): `y ↦ (x ↦ ∫ y x dμ)` is an isometric isomorphism from `L_q`
  onto `L_p*` (`dualLp`).

Proof, for `φ ∈ L_p*`:
* `dualSignedMeasure`: `A ↦ φ(1_A)` is a signed measure. Countable additivity comes from
  `hasSum_indicatorConstLp`: indicators of disjoint unions converge in `L_p`.
* It is absolutely continuous with respect to `μ` (`dualSignedMeasure_ac`). Its Radon–Nikodym
  density `g = dualDensity` satisfies `∫_A g = φ(1_A)` (`setIntegral_dualDensity`), and
  `φ(s) = ∫ g s` for simple `s` (`dualDensity_simpleFunc`).
* `eLpNorm_dualDensity_le`: `‖g‖_q ≤ ‖φ‖`. Take simple `sₖ → g` with the sign of `g` and
  `|sₖ| ≤ |g|` (`signedApprox`). The test functions `sgn(sₖ)|sₖ|^{q−1}` give
  `∫ |sₖ|^q ≤ ‖φ‖^q`, and Fatou's lemma gives the bound for `g`.
* `exists_preimage_pairLqLp`: `φ = (x ↦ ∫ g x)`, because both sides are continuous and agree
  on indicators, which are dense in `L_p`. `pairLqLp_injective` gives injectivity for every
  σ-finite measure.

σ-finite and arbitrary measures, `1 < p < ∞`: see `DualLpSigmaFinite`
(`example_15_4_sigmaFinite`, `example_15_4_general`).
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Metric Set MeasureTheory Function
open scoped ENNReal symmDiff

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The finite unions of disjoint sets give sums of indicators. -/
theorem indicatorConstLp_biUnion [IsFiniteMeasure μ] {f : ℕ → Set Z} (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise (Disjoint on f)) (s : Finset ℕ) :
    indicatorConstLp p (s.measurableSet_biUnion fun i _ => hf i) (measure_ne_top μ _) (1 : ℝ) =
      ∑ i ∈ s, indicatorConstLp p (hf i) (measure_ne_top μ _) (1 : ℝ) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine Lp.ext ?_
    filter_upwards [indicatorConstLp_coeFn (p := p) (μ := μ) (c := (1 : ℝ))
      (hs := Finset.measurableSet_biUnion (∅ : Finset ℕ) fun i _ => hf i)
      (hμs := measure_ne_top μ _), Lp.coeFn_zero ℝ p μ] with z h1 h2
    rw [h1, h2]; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    refine Lp.ext ?_
    filter_upwards [indicatorConstLp_coeFn (p := p) (μ := μ) (c := (1 : ℝ))
      (hs := Finset.measurableSet_biUnion (insert a s) fun i _ => hf i)
      (hμs := measure_ne_top μ _),
      Lp.coeFn_add (indicatorConstLp p (hf a) (measure_ne_top μ _) (1 : ℝ))
        (indicatorConstLp p (s.measurableSet_biUnion fun i _ => hf i) (measure_ne_top μ _) 1),
      indicatorConstLp_coeFn (p := p) (μ := μ) (c := (1 : ℝ)) (hs := hf a)
        (hμs := measure_ne_top μ _),
      indicatorConstLp_coeFn (p := p) (μ := μ) (c := (1 : ℝ))
        (hs := s.measurableSet_biUnion fun i _ => hf i) (hμs := measure_ne_top μ _)]
      with z h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4, Finset.set_biUnion_insert]
    have hdis : Disjoint (f a) (⋃ i ∈ s, f i) := by
      rw [Set.disjoint_iUnion₂_right]
      exact fun i hi => hd (fun h => ha (h ▸ hi))
    rw [Set.indicator_union_of_disjoint hdis]


/-- The disjoint unions converge in `Lp`. -/
theorem hasSum_indicatorConstLp [IsFiniteMeasure μ] (hp : p ≠ ∞) {f : ℕ → Set Z}
    (hf : ∀ i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) :
    HasSum (fun i => indicatorConstLp p (hf i) (measure_ne_top μ _) (1 : ℝ))
      (indicatorConstLp p (MeasurableSet.iUnion hf) (measure_ne_top μ _) (1 : ℝ)) := by
  unfold HasSum
  have e : (fun s : Finset ℕ => ∑ i ∈ s, indicatorConstLp p (hf i) (measure_ne_top μ _) (1 : ℝ)) =
      fun s => indicatorConstLp p (s.measurableSet_biUnion fun i _ => hf i) (measure_ne_top μ _)
        (1 : ℝ) := funext fun s => (indicatorConstLp_biUnion hf hd s).symm
  rw [e]
  refine tendsto_indicatorConstLp_set hp ?_
  have hsub : ∀ s : Finset ℕ, (⋃ i ∈ s, f i) ⊆ ⋃ i, f i := fun s =>
    iUnion₂_subset fun i _ => subset_iUnion f i
  have e2 : ∀ s : Finset ℕ, (⋃ i ∈ s, f i) ∆ (⋃ i, f i) = (⋃ i, f i) \ ⋃ i ∈ s, f i :=
    fun s => symmDiff_of_le (hsub s)
  simp only [e2]
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := fun s : Finset ℕ =>
      (⋃ i, f i) \ ⋃ i ∈ s, f i)
    (fun s => ((MeasurableSet.iUnion hf).diff
      (s.measurableSet_biUnion fun i _ => hf i)).nullMeasurableSet)
    (fun s t hst z hz => ⟨hz.1, fun h' => hz.2 (by
      obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 h'
      exact mem_iUnion₂.2 ⟨i, hst hi, hzi⟩)⟩)
    ⟨∅, measure_ne_top μ _⟩
  have hempty : (⋂ s : Finset ℕ, (⋃ i, f i) \ ⋃ i ∈ s, f i) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 (mem_iInter.1 hz ∅).1
    exact (mem_iInter.1 hz {i}).2 (mem_iUnion₂.2 ⟨i, Finset.mem_singleton_self i, hi⟩)
  rw [hempty, measure_empty] at hlim
  exact hlim

open Classical in
/-- The signed measure `A ↦ φ(1_A)` of a functional `φ ∈ L_p*`, for a finite measure. -/
noncomputable def dualSignedMeasure [IsFiniteMeasure μ] (hp : p ≠ ∞)
    (φ : StrongDual ℝ (Lp ℝ p μ)) : SignedMeasure Z where
  measureOf' A := if h : MeasurableSet A then φ (indicatorConstLp p h (measure_ne_top μ A) 1)
    else 0
  empty' := by
    simp only [MeasurableSet.empty, ↓reduceDIte]
    rw [indicatorConstLp_empty, map_zero]
  not_measurable' A hA := by simp [hA]
  m_iUnion' f hf hd := by
    simp only [MeasurableSet.iUnion hf, hf, ↓reduceDIte]
    exact (hasSum_indicatorConstLp hp hf hd).mapL φ


/-- `dualSignedMeasure hp φ A = φ(1_A)` for measurable `A`. -/
theorem dualSignedMeasure_apply [IsFiniteMeasure μ] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ))
    {A : Set Z} (hA : MeasurableSet A) :
    dualSignedMeasure hp φ A = φ (indicatorConstLp p hA (measure_ne_top μ A) 1) := by
  simp [dualSignedMeasure, hA]

omit [Fact (1 ≤ p)] in
/-- The indicator of a null set is `0` in `L_p`. -/
theorem indicatorConstLp_eq_zero_of_null {A : Set Z} (hA : MeasurableSet A) (hμA : μ A = 0)
    (c : ℝ) : indicatorConstLp (μ := μ) p hA (by simp [hμA]) c = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [indicatorConstLp_coeFn (p := p) (μ := μ) (c := c) (hs := hA)
    (hμs := by simp [hμA]), measure_eq_zero_iff_ae_notMem.1 hμA] with z h1 h2
  rw [h1, indicator_of_notMem h2]; rfl

/-- `A ↦ φ(1_A)` is absolutely continuous with respect to `μ`. -/
theorem dualSignedMeasure_ac [IsFiniteMeasure μ] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    dualSignedMeasure hp φ ≪ᵥ μ.toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk fun A hA h0 => ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at h0
  rw [dualSignedMeasure_apply hp φ hA, indicatorConstLp_eq_zero_of_null hA h0, map_zero]

/-- The Radon–Nikodym density of `A ↦ φ(1_A)`. -/
noncomputable def dualDensity [IsFiniteMeasure μ] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    Z → ℝ :=
  (dualSignedMeasure hp φ).rnDeriv μ

/-- The density of `A ↦ φ(1_A)` is integrable. -/
theorem integrable_dualDensity [IsFiniteMeasure μ] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    Integrable (dualDensity hp φ) μ := SignedMeasure.integrable_rnDeriv _ _

/-- `∫_A g dμ = φ(1_A)` for the density `g` of `A ↦ φ(1_A)`. -/
theorem setIntegral_dualDensity [IsFiniteMeasure μ] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ))
    {A : Set Z} (hA : MeasurableSet A) :
    ∫ z in A, dualDensity hp φ z ∂μ = φ (indicatorConstLp p hA (measure_ne_top μ A) 1) := by
  rw [← dualSignedMeasure_apply hp φ hA,
    ← SignedMeasure.withDensityᵥ_rnDeriv_eq _ μ (dualSignedMeasure_ac hp φ)]
  exact (withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hA).symm


omit [Fact (1 ≤ p)] in
/-- `1_A c = c · 1_A` in `L_p`. -/
theorem indicatorConstLp_eq_smul {A : Set Z} (hA : MeasurableSet A) (hμA : μ A ≠ ∞) (c : ℝ) :
    indicatorConstLp p hA hμA c = c • indicatorConstLp p hA hμA (1 : ℝ) := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hA) (hμs := hμA) (c := c),
    Lp.coeFn_smul c (indicatorConstLp p hA hμA (1 : ℝ)),
    indicatorConstLp_coeFn (p := p) (hs := hA) (hμs := hμA) (c := (1 : ℝ))] with z h1 h2 h3
  rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
  by_cases hz : z ∈ A <;> simp [hz]

/-- `φ(s) = ∫ g s` for simple `s`, where `g` is the density of `A ↦ φ(1_A)`. -/
theorem dualDensity_simpleFunc [IsFiniteMeasure μ] (hp : p ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ))
    (s : SimpleFunc Z ℝ) :
    φ ((s.memLp_of_isFiniteMeasure p μ).toLp s) = ∫ z, dualDensity hp φ z * s z ∂μ := by
  induction s using SimpleFunc.induction with
  | const c hA =>
    rename_i A
    have e : (SimpleFunc.memLp_of_isFiniteMeasure
        (SimpleFunc.piecewise A hA (SimpleFunc.const Z c) (SimpleFunc.const Z 0)) p μ).toLp _ =
        indicatorConstLp p hA (measure_ne_top μ A) c := by
      refine Lp.ext ?_
      filter_upwards [MemLp.coeFn_toLp (SimpleFunc.memLp_of_isFiniteMeasure
        (SimpleFunc.piecewise A hA (SimpleFunc.const Z c) (SimpleFunc.const Z 0)) p μ),
        indicatorConstLp_coeFn (p := p) (μ := μ) (c := c) (hs := hA)
          (hμs := measure_ne_top μ A)] with z h1 h2
      rw [h1, h2, SimpleFunc.coe_piecewise]
      by_cases hz : z ∈ A <;> simp [hz]
    rw [e, indicatorConstLp_eq_smul, map_smul, smul_eq_mul,
      ← setIntegral_dualDensity hp φ hA, ← integral_const_mul, ← integral_indicator hA]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    rw [SimpleFunc.coe_piecewise]
    by_cases hz : z ∈ A <;> simp [hz, mul_comm]
  | @add f g _ hf hg =>
    have hfi : Integrable (fun z => dualDensity hp φ z * f z) μ :=
      (integrable_dualDensity hp φ).mul_of_top_left (f.memLp_top μ)
    have hgi : Integrable (fun z => dualDensity hp φ z * g z) μ :=
      (integrable_dualDensity hp φ).mul_of_top_left (g.memLp_top μ)
    have e : (SimpleFunc.memLp_of_isFiniteMeasure (f + g) p μ).toLp _ =
        (f.memLp_of_isFiniteMeasure p μ).toLp f + (g.memLp_of_isFiniteMeasure p μ).toLp g :=
      MemLp.toLp_add _ _
    rw [e, map_add, hf, hg, ← integral_add hfi hgi]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp [mul_add]


/-- The simple approximants `(g⁺)ₖ − (g⁻)ₖ` of a real function `g`, built from `eapprox`. -/
noncomputable def signedApprox (g : Z → ℝ) (k : ℕ) : SimpleFunc Z ℝ :=
  (SimpleFunc.eapprox (fun z => ENNReal.ofReal (g z)) k).map ENNReal.toReal -
    (SimpleFunc.eapprox (fun z => ENNReal.ofReal (-g z)) k).map ENNReal.toReal

/-- `eapprox f k ≤ f`. -/
theorem eapprox_le_self {f : Z → ℝ≥0∞} (hf : Measurable f) (k : ℕ) (z : Z) :
    SimpleFunc.eapprox f k z ≤ f z :=
  (le_iSup (fun n => SimpleFunc.eapprox f n z) k).trans_eq (SimpleFunc.iSup_eapprox_apply hf z)

/-- `eapprox f k → f` pointwise. -/
theorem tendsto_eapprox_apply {f : Z → ℝ≥0∞} (hf : Measurable f) (z : Z) :
    Tendsto (fun k => SimpleFunc.eapprox f k z) atTop (𝓝 (f z)) := by
  rw [← SimpleFunc.iSup_eapprox_apply hf z]
  exact tendsto_atTop_iSup fun m n h => SimpleFunc.monotone_eapprox f h z

/-- `signedApprox g k` has the sign of `g` and lies between `0` and `g`. -/
theorem signedApprox_bounds {g : Z → ℝ} (hg : Measurable g) (k : ℕ) (z : Z) :
    (0 ≤ g z → 0 ≤ signedApprox g k z ∧ signedApprox g k z ≤ g z) ∧
      (g z < 0 → g z ≤ signedApprox g k z ∧ signedApprox g k z ≤ 0) := by
  have hgn : Measurable fun z => -g z := hg.neg
  have hp := eapprox_le_self hg.ennreal_ofReal k z
  have hn := eapprox_le_self hgn.ennreal_ofReal k z
  simp only [signedApprox, SimpleFunc.coe_sub, SimpleFunc.coe_map, Pi.sub_apply,
    Function.comp_apply]
  constructor
  · intro h
    have h0 : SimpleFunc.eapprox (fun z => ENNReal.ofReal (-g z)) k z = 0 := by
      have : ENNReal.ofReal (-g z) = 0 := ENNReal.ofReal_eq_zero.2 (by linarith)
      exact le_antisymm (hn.trans this.le) bot_le
    rw [h0, ENNReal.toReal_zero, sub_zero]
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal h hp⟩
  · intro h
    have h0 : SimpleFunc.eapprox (fun z => ENNReal.ofReal (g z)) k z = 0 := by
      have : ENNReal.ofReal (g z) = 0 := ENNReal.ofReal_eq_zero.2 h.le
      exact le_antisymm (hp.trans this.le) bot_le
    rw [h0, ENNReal.toReal_zero, zero_sub]
    set e := (SimpleFunc.eapprox (fun z => ENNReal.ofReal (-g z)) k z).toReal
    have h1 : e ≤ -g z := ENNReal.toReal_le_of_le_ofReal (by linarith) hn
    have h2 : 0 ≤ e := ENNReal.toReal_nonneg
    exact ⟨by linarith, by linarith⟩

/-- `signedApprox g k → g` pointwise. -/
theorem tendsto_signedApprox {g : Z → ℝ} (hg : Measurable g) (z : Z) :
    Tendsto (fun k => signedApprox g k z) atTop (𝓝 (g z)) := by
  have h1 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp
    (tendsto_eapprox_apply hg.ennreal_ofReal z)
  have hgn : Measurable fun z => -g z := hg.neg
  have h2 := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp
    (tendsto_eapprox_apply hgn.ennreal_ofReal z)
  have := h1.sub h2
  simp only [ENNReal.toReal_ofReal', max_zero_sub_eq_self] at this
  simpa [signedApprox] using this


/-- If `0 ≤ S ≤ C S^{1/P}` with `1/P + 1/Q = 1`, then `S ≤ C^Q`. -/
theorem le_rpow_of_le_mul_rpow {P Q S C : ℝ} (hPQ : P.HolderConjugate Q) (hS0 : 0 ≤ S)
    (hC : 0 ≤ C) (hb : S ≤ C * S ^ (1 / P)) : S ≤ C ^ Q := by
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have hsplit : S = S ^ (1 / P) * S ^ (1 / Q) := by
      have h11 : 1 / P + 1 / Q = 1 := by rw [one_div, one_div, hPQ.inv_add_inv_eq_one]
      rw [← Real.rpow_add hpos, h11, Real.rpow_one]
    have h1 : S ^ (1 / Q) ≤ C := by
      have hp' : 0 < S ^ (1 / P) := Real.rpow_pos_of_pos hpos _
      nth_rewrite 1 [hsplit] at hb
      rw [mul_comm (S ^ (1 / P)) (S ^ (1 / Q))] at hb
      exact le_of_mul_le_mul_right hb hp'
    calc S = (S ^ (1 / Q)) ^ Q := by
          rw [← Real.rpow_mul hS0, one_div_mul_cancel hPQ.symm.ne_zero, Real.rpow_one]
      _ ≤ C ^ Q := Real.rpow_le_rpow (by positivity) h1 hPQ.symm.nonneg

/-- The density `g` of `A ↦ φ(1_A)` lies in `L_q` with `‖g‖_q ≤ ‖φ‖`. The test functions are
`sgn(sₖ)|sₖ|^{q−1}` for simple `sₖ → g` with the sign of `g` and `|sₖ| ≤ |g|`; then Fatou's
lemma. -/
theorem eLpNorm_dualDensity_le [IsFiniteMeasure μ] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    [p.HolderConjugate q]
    (hp : p ≠ ∞) (hq : q ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) :
    eLpNorm (dualDensity hp φ) q μ ≤ ENNReal.ofReal ‖φ‖ := by
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  set P := p.toReal
  set Q := q.toReal
  set g := dualDensity hp φ with hgdef
  have hgm : Measurable g := SignedMeasure.measurable_rnDeriv _ _
  set s := signedApprox g
  have hsb : ∀ k z, (0 ≤ g z → 0 ≤ s k z ∧ s k z ≤ g z) ∧
      (g z < 0 → g z ≤ s k z ∧ s k z ≤ 0) := signedApprox_bounds hgm
  have hst : ∀ z, Tendsto (fun k => s k z) atTop (𝓝 (g z)) := tendsto_signedApprox hgm
  let F : ℝ → ℝ := fun t => if 0 ≤ t then t ^ (Q - 1) else -((-t) ^ (Q - 1))
  have hQ1 : 0 < Q - 1 := hPQ.symm.sub_one_pos
  have hQP : (Q - 1) * P = Q := hPQ.symm.sub_one_mul_conj
  have hpow : ∀ t : ℝ, 0 ≤ t → t ^ Q = t ^ (Q - 1) * t := fun t ht => by
    conv_lhs => rw [show Q = (Q - 1) + 1 by ring]
    rw [Real.rpow_add' ht (by linarith), Real.rpow_one]
  have hF1 : ∀ t : ℝ, |F t| = |t| ^ (Q - 1) := fun t => by
    simp only [F]
    split_ifs with h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.rpow_nonneg h _)]
    · rw [abs_neg, abs_of_nonneg (Real.rpow_nonneg (by linarith) _), abs_of_neg (not_le.1 h)]
  have hF2 : ∀ k z, |s k z| ^ Q ≤ g z * F (s k z) := fun k z => by
    obtain ⟨hpos, hneg⟩ := hsb k z
    by_cases hg0 : 0 ≤ g z
    · obtain ⟨h1, h2⟩ := hpos hg0
      simp only [F, h1, ↓reduceIte]
      rw [abs_of_nonneg h1, hpow _ h1, mul_comm]
      exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg h1 _)
    · obtain ⟨h1, h2⟩ := hneg (not_le.1 hg0)
      rcases h2.lt_or_eq with h3 | h3
      · simp only [F, not_le.2 h3, ↓reduceIte]
        rw [abs_of_neg h3, hpow _ (by linarith), mul_comm]
        have : 0 ≤ (-(s k z)) ^ (Q - 1) := Real.rpow_nonneg (by linarith) _
        nlinarith
      · rw [h3]
        simp only [F, le_refl, ↓reduceIte, abs_zero]
        rw [Real.zero_rpow (by linarith), Real.zero_rpow hQ1.ne', mul_zero]
  have hi1 : ∀ k, Integrable (fun z => |s k z| ^ Q) μ := fun k =>
    ((s k).map fun t => |t| ^ Q).integrable_of_isFiniteMeasure
  have hS : ∀ k, ∫ z, |s k z| ^ Q ∂μ ≤ ‖φ‖ ^ Q := fun k => by
    set x := (s k).map F
    have hxm := x.memLp_of_isFiniteMeasure p μ
    have hi2 : Integrable (fun z => g z * x z) μ :=
      (integrable_dualDensity hp φ).mul_of_top_left (x.memLp_top μ)
    have h1 : ∫ z, |s k z| ^ Q ∂μ ≤ φ (hxm.toLp x) := by
      rw [dualDensity_simpleFunc]
      exact integral_mono (hi1 k) hi2 fun z => by
        rw [SimpleFunc.map_apply]; exact hF2 k z
    have h2 : ‖hxm.toLp x‖ = (∫ z, |s k z| ^ Q ∂μ) ^ (1 / P) := by
      rw [Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm (ne_zero_of_lt
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p))) hp hxm,
        ENNReal.toReal_ofReal (by positivity), one_div]
      congr 2
      ext z
      rw [SimpleFunc.map_apply, Real.norm_eq_abs, hF1, ← Real.rpow_mul (abs_nonneg _), hQP]
    refine le_rpow_of_le_mul_rpow hPQ (integral_nonneg fun z => by positivity) (norm_nonneg _) ?_
    calc ∫ z, |s k z| ^ Q ∂μ ≤ φ (hxm.toLp x) := h1
      _ ≤ ‖φ‖ * ‖hxm.toLp x‖ := (le_abs_self _).trans (φ.le_opNorm _)
      _ = _ := by rw [h2]
  have hlim : ∀ z, Tendsto (fun k => ENNReal.ofReal (|s k z| ^ Q)) atTop
      (𝓝 (ENNReal.ofReal (|g z| ^ Q))) := fun z =>
    (ENNReal.continuous_ofReal.tendsto _).comp
      (((continuous_abs.tendsto _).comp (hst z)).rpow_const
        (Or.inr hPQ.symm.nonneg))
  have hfat : ∫⁻ z, ENNReal.ofReal (|g z| ^ Q) ∂μ ≤ ENNReal.ofReal (‖φ‖ ^ Q) := by
    calc ∫⁻ z, ENNReal.ofReal (|g z| ^ Q) ∂μ
        = ∫⁻ z, liminf (fun k => ENNReal.ofReal (|s k z| ^ Q)) atTop ∂μ :=
          lintegral_congr fun z => (hlim z).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ z, ENNReal.ofReal (|s k z| ^ Q) ∂μ) atTop :=
          lintegral_liminf_le' fun k =>
            (((s k).map fun t => ENNReal.ofReal (|t| ^ Q)).measurable).aemeasurable
      _ ≤ ENNReal.ofReal (‖φ‖ ^ Q) := by
          refine (liminf_le_liminf (Eventually.of_forall fun k => ?_)).trans
            (liminf_const _).le
          rw [← ofReal_integral_eq_lintegral_ofReal (hi1 k)
            (Eventually.of_forall fun z => by positivity)]
          exact ENNReal.ofReal_le_ofReal (hS k)
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq hgm.aestronglyMeasurable]
  have e : ∀ z, ‖g z‖ₑ ^ Q = ENNReal.ofReal (|g z| ^ Q) := fun z => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hPQ.symm.nonneg]
  change (∫⁻ z, ‖g z‖ₑ ^ Q ∂μ) ^ (1 / Q) ≤ _
  rw [lintegral_congr fun z => e z]
  calc (∫⁻ z, ENNReal.ofReal (|g z| ^ Q) ∂μ) ^ (1 / Q) ≤ ENNReal.ofReal (‖φ‖ ^ Q) ^ (1 / Q) :=
        ENNReal.rpow_le_rpow hfat (by positivity)
    _ = ENNReal.ofReal ‖φ‖ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
          ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hPQ.symm.ne_zero, Real.rpow_one]


variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The pairing `(y, x) ↦ ∫ y x dμ` of `L_q` with `L_p` (Mathlib's `lpPairing`). -/
noncomputable def pairLqLp (μ : Measure Z) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] : Lp ℝ q μ →L[ℝ] Lp ℝ p μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p

/-- `pairLqLp μ p q y x = ∫ y x dμ`. -/
theorem pairLqLp_apply (y : Lp ℝ q μ) (x : Lp ℝ p μ) :
    pairLqLp μ p q y x = ∫ z, y z * x z ∂μ := by
  rw [pairLqLp, ContinuousLinearMap.lpPairing_eq_integral]; rfl

/-- Hölder's inequality: `|∫ y x dμ| ≤ ‖y‖_q ‖x‖_p`. -/
theorem abs_pairLqLp_le (y : Lp ℝ q μ) (x : Lp ℝ p μ) : |pairLqLp μ p q y x| ≤ ‖y‖ * ‖x‖ := by
  have h1 : pairLqLp μ p q y x = L1.integral ((ContinuousLinearMap.mul ℝ ℝ).holder 1 y x) := by
    rw [pairLqLp_apply, L1.integral_eq_integral]
    exact integral_congr_ae ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder y x).symm
  rw [h1, ← Real.norm_eq_abs]
  refine (L1.norm_integral_le _).trans ?_
  refine ((ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le y x).trans ?_
  have := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖y‖ * ‖x‖ ≤ 1 * ‖y‖ * ‖x‖ := by gcongr
    _ = ‖y‖ * ‖x‖ := by rw [one_mul]

/-- `∫ y (c 1_A) dμ = (∫_A y dμ) c`. -/
theorem pairLqLp_indicator (y : Lp ℝ q μ) {A : Set Z} (hA : MeasurableSet A) (hμA : μ A ≠ ∞)
    (c : ℝ) : pairLqLp μ p q y (indicatorConstLp p hA hμA c) = (∫ z in A, y z ∂μ) * c := by
  rw [pairLqLp_apply, ← integral_mul_const, ← integral_indicator hA]
  refine integral_congr_ae ?_
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hA) (hμs := hμA) (c := c)] with z hz
  rw [hz]
  by_cases h : z ∈ A <;> simp [h]

/-- For a σ-finite measure, `y ↦ (x ↦ ∫ y x dμ)` is injective from `L_q` to `L_p*`. -/
theorem pairLqLp_injective [SigmaFinite μ] : Function.Injective (pairLqLp μ p q) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  have hint : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (fun z => y z) s μ :=
    fun s hs hμs => by
      have : Fact (μ s < ∞) := ⟨hμs⟩
      have hm : MemLp (fun z => y z) q (μ.restrict s) := (Lp.memLp y).restrict s
      exact hm.integrable Fact.out
  have h0 := ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite hint fun s hs hμs => by
    have := pairLqLp_indicator (p := p) y hs hμs.ne 1
    rw [hy, mul_one] at this
    exact this.symm
  exact (Lp.eq_zero_iff_ae_eq_zero).2 h0

/-- For a finite measure and `1 < p < ∞`, every `φ ∈ L_p*` is `x ↦ ∫ y x dμ` for some
`y ∈ L_q` with `‖y‖_q ≤ ‖φ‖`; `y` is the Radon–Nikodym density of `A ↦ φ(1_A)`. -/
theorem exists_preimage_pairLqLp [IsFiniteMeasure μ] (hp : p ≠ ∞) (hq : q ≠ ∞)
    (φ : StrongDual ℝ (Lp ℝ p μ)) :
    ∃ y : Lp ℝ q μ, pairLqLp μ p q y = φ ∧ ‖y‖ ≤ ‖φ‖ := by
  have hb := eLpNorm_dualDensity_le hp hq φ
  have hm : MemLp (dualDensity hp φ) q μ := memLp_iff.2 (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)
  refine ⟨hm.toLp _, ?_, ?_⟩
  · refine (Lp.induction (p := p) hp (fun x => pairLqLp μ p q (hm.toLp _) x = φ x) ?_ ?_
      (isClosed_eq (pairLqLp μ p q (hm.toLp _)).continuous φ.continuous) ·) |>
      ContinuousLinearMap.ext
    · intro c s hs hμs
      rw [Lp.simpleFunc.coe_indicatorConst, pairLqLp_indicator, indicatorConstLp_eq_smul,
        map_smul, smul_eq_mul, ← setIntegral_dualDensity hp φ hs, mul_comm]
      congr 1
      exact setIntegral_congr_ae hs (by
        filter_upwards [hm.coeFn_toLp] with z hz _ using hz)
    · intro f f' hf hf' _ h1 h2
      simp only [map_add, h1, h2]
  · rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) hb

/-- For a finite measure and `1 < p < ∞`, `y ↦ (x ↦ ∫ y x dμ)` preserves norms. -/
theorem norm_pairLqLp [IsFiniteMeasure μ] (hp : p ≠ ∞) (hq : q ≠ ∞) (y : Lp ℝ q μ) :
    ‖pairLqLp μ p q y‖ = ‖y‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
      rw [Real.norm_eq_abs]; exact abs_pairLqLp_le y x
  · obtain ⟨y', hy', hn⟩ := exists_preimage_pairLqLp hp hq (pairLqLp μ p q y)
    calc ‖y‖ = ‖y'‖ := by rw [pairLqLp_injective hy']
      _ ≤ ‖pairLqLp μ p q y‖ := hn

/-- `L_p* = L_q` for a finite measure and conjugate `1 < p, q < ∞`. -/
noncomputable def dualLp [IsFiniteMeasure μ] (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ) :=
  LinearIsometryEquiv.ofSurjective ⟨(pairLqLp μ p q).toLinearMap, norm_pairLqLp hp hq⟩
    fun φ => (exists_preimage_pairLqLp hp hq φ).imp fun _ h => h.1

/-- **Example 4** (pp. 449–450): for a finite measure and `1 < p < ∞` with `1/p + 1/q = 1`, the
dual of `L_p(Z, 𝒵, μ)` is `L_q(Z, 𝒵, μ)`. Each `y ∈ L_q` gives `x ↦ ∫ y x dμ` in `L_p*`,
every element of `L_p*` arises from exactly one `y`, and norms are preserved. -/
theorem example_15_4 [IsFiniteMeasure μ] (hp : p ≠ ∞) (hq : q ≠ ∞) :
    ∃ e : Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ), ∀ y x, e y x = ∫ z, y z * x z ∂μ :=
  ⟨dualLp hp hq, fun y x => pairLqLp_apply y x⟩

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The dual of `L_p` for `1 < p < ∞` on σ-finite and arbitrary measure spaces

SLP §15.1, Example 4, pp. 449–450: for `1 < p < ∞` and `1/p + 1/q = 1` the dual of
`L_p(Z, 𝒵, μ)` is `L_q(Z, 𝒵, μ)`. `DualLp` proves this for finite `μ` (`example_15_4`). Here it
is proved for σ-finite `μ`, and then for every measure `μ`, which is the book's claim in full for
`1 < p < ∞`. (For `p = 1` the claim needs σ-finiteness: `l1_dual_counterexample`.)

* **Example 4, σ-finite** (`example_15_4_sigmaFinite`): `y ↦ (x ↦ ∫ y x dμ)` is an isometric
  isomorphism from `L_q` onto `L_p*` (`dualLpSigmaFinite`).
* **Example 4, any measure** (`example_15_4_general`): the same with no finiteness or
  σ-finiteness assumption (`dualLpOfNeTop`).
* `norm_pairLqLp_eq`, `pairLqLp_injective_of_ne_top`: for every `μ`, `y ↦ (x ↦ ∫ y x dμ)`
  preserves norms and is injective.

Proof.
* `isDualRep_of_weight`: let `w ≥ 0` be integrable and vanish exactly off `S`. The measure `w μ`
  is finite, and `x ↦ w^{1/p} x` is an isometry of `L_p(w μ)` into `L_p(μ)`
  (`eLpNorm_rpow_mul`). `example_15_4`'s `exists_preimage_pairLqLp` represents
  `x ↦ φ(w^{1/p} x)` by some `g ∈ L_q(w μ)`, and `y = w^{1/q} g` represents `φ` on functions
  vanishing off `S` (`IsDualRep`).
* σ-finite `μ`: take `w > 0` everywhere (`exists_pos_lintegral_lt_of_sigmaFinite`), `S = Z`.
* The test function `sgn(y)|y|^{q−1}` (`testFn`) gives `∫ |y|^q ≤ ‖φ‖^q` for every
  representing `y` (`IsDualRep.integral_le`), hence the norm identity, and uniqueness of the
  representation on each `S` (`IsDualRep.ae_eq`).
* Any `μ` (`exists_preimage_pairLqLp_of_ne_top`): each `u ∈ L_p` vanishes off a set on which `μ`
  is σ-finite (`exists_sigmaFinite_support`), and on each such set `S` there is a
  representation `y_S` (`exists_isDualRep`). Take a countable union `S*` of such sets along
  which `∫ |y_S|^q` tends to its supremum (`sigmaFinite_restrict_iUnion`). For `u ∈ L_p` with
  σ-finite support `t`, the representation on `S* ∪ t` restricts to `y_{S*}` on `S*`
  (`IsDualRep.indicator`, `IsDualRep.ae_eq`), and maximality forces it to vanish off `S*`, so
  `φ(u) = ∫ y_{S*} u dμ`.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Metric Set MeasureTheory Function
open scoped ENNReal NNReal

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

/-- Weighting by `w ^ a`, `a ≠ 0`, turns `μ.withDensity w`-a.e. equality into `μ`-a.e.
equality. -/
theorem ae_eq_rpow_mul_of_withDensity {w : Z → ℝ≥0} (hw : Measurable w) {a : ℝ} (ha : a ≠ 0)
    {f f' : Z → ℝ} (h : f =ᵐ[μ.withDensity fun z => (w z : ℝ≥0∞)] f') :
    (fun z => ((w z ^ a : ℝ≥0) : ℝ) * f z) =ᵐ[μ] fun z => ((w z ^ a : ℝ≥0) : ℝ) * f' z := by
  have h' := (ae_withDensity_iff hw.coe_nnreal_ennreal).1 h
  filter_upwards [h'] with z hz
  by_cases h0 : w z = 0
  · simp [h0, NNReal.zero_rpow ha]
  · rw [hz (by simpa using h0)]

/-- `‖w^{1/r} f‖_{L_r(μ)} = ‖f‖_{L_r(w μ)}`. -/
theorem eLpNorm_rpow_mul {w : Z → ℝ≥0} (hw : Measurable w) {r : ℝ≥0∞} (hr0 : r ≠ 0)
    (hrt : r ≠ ∞) {f : Z → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun z => ((w z ^ (1 / r.toReal) : ℝ≥0) : ℝ) * f z) r μ =
      eLpNorm f r (μ.withDensity fun z => (w z : ℝ≥0∞)) := by
  have hR : 0 < r.toReal := ENNReal.toReal_pos hr0 hrt
  have hwm : Measurable fun z => ((w z ^ (1 / r.toReal) : ℝ≥0) : ℝ) :=
    (hw.pow_const _).coe_nnreal_real
  have hm : AEStronglyMeasurable (fun z => ((w z ^ (1 / r.toReal) : ℝ≥0) : ℝ) * f z) μ :=
    hwm.aestronglyMeasurable.mul hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrt hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrt
      (hf.mono_ac (withDensity_absolutelyContinuous _ _)),
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hw.coe_nnreal_ennreal
      (ae_of_all _ fun z => ENNReal.coe_lt_top)]
  congr 1
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply]
  rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hR.le]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, NNReal.abs_eq, ENNReal.ofReal_coe_nnreal,
    ← ENNReal.coe_rpow_of_nonneg _ hR.le, ← NNReal.rpow_mul, one_div_mul_cancel hR.ne',
    NNReal.rpow_one]

/-- `w^a w^{-a} t = t` where `w ≠ 0`, and `= 0` where `w = 0`. -/
theorem rpow_mul_rpow_neg_mul (x : ℝ≥0) {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    ((x ^ a : ℝ≥0) : ℝ) * (((x ^ (-a) : ℝ≥0) : ℝ) * t) = if x = 0 then 0 else t := by
  by_cases h0 : x = 0
  · simp [h0, NNReal.zero_rpow ha]
  · rw [← mul_assoc, ← NNReal.coe_mul, NNReal.rpow_neg, mul_inv_cancel₀ (by positivity)]
    simp [h0]

/-- If `f ∈ L_r(w μ)`, then `w^{1/r} f ∈ L_r(μ)`. -/
theorem memLp_rpow_mul {w : Z → ℝ≥0} (hw : Measurable w) {r : ℝ≥0∞} (hr0 : r ≠ 0)
    (hrt : r ≠ ∞) {f : Z → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfm : MemLp f r (μ.withDensity fun z => (w z : ℝ≥0∞))) :
    MemLp (fun z => ((w z ^ (1 / r.toReal) : ℝ≥0) : ℝ) * f z) r μ :=
  by rw [memLp_iff, eLpNorm_rpow_mul hw hr0 hrt hf]; exact hfm

/-- If `u ∈ L_r(μ)`, then `w^{-1/r} u ∈ L_r(w μ)`. -/
theorem memLp_rpow_neg_mul {w : Z → ℝ≥0} (hw : Measurable w) {r : ℝ≥0∞} (hr0 : r ≠ 0)
    (hrt : r ≠ ∞) {u : Z → ℝ} (hu : MemLp u r μ) :
    MemLp (fun z => ((w z ^ (-(1 / r.toReal)) : ℝ≥0) : ℝ) * u z) r
      (μ.withDensity fun z => (w z : ℝ≥0∞)) := by
  have hR : 0 < r.toReal := ENNReal.toReal_pos hr0 hrt
  have hm : AEStronglyMeasurable (fun z => ((w z ^ (-(1 / r.toReal)) : ℝ≥0) : ℝ) * u z) μ :=
    (hw.pow_const _).coe_nnreal_real.aestronglyMeasurable.mul hu.aestronglyMeasurable
  rw [memLp_iff, ← eLpNorm_rpow_mul hw hr0 hrt hm]
  refine lt_of_le_of_lt (eLpNorm_mono
    ((hw.pow_const _).coe_nnreal_real.aestronglyMeasurable.mul hm) fun z => ?_) hu
  rw [rpow_mul_rpow_neg_mul _ (by positivity)]
  split_ifs <;> simp

/-- `y` represents `φ ∈ L_p*` on the set `S`: `y ∈ L_r` vanishes off `S`, and
`φ(u) = ∫ y u dμ` for every `u ∈ L_p` vanishing a.e. off `S`. -/
def IsDualRep {p : ℝ≥0∞} [Fact (1 ≤ p)] (φ : StrongDual ℝ (Lp ℝ p μ)) (r : ℝ≥0∞) (S : Set Z)
    (y : Z → ℝ) : Prop :=
  MemLp y r μ ∧ (∀ z, z ∉ S → y z = 0) ∧
    ∀ u : Lp ℝ p μ, (∀ᵐ z ∂μ, z ∉ S → u z = 0) → φ u = ∫ z, y z * u z ∂μ

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The representation on a weight's support: if `w ≥ 0` is integrable and vanishes exactly off
`S`, then every `φ ∈ L_p*` is represented on `S` by some `y`. Apply `exists_preimage_pairLqLp`
to the finite measure `w μ` and the functional `x ↦ φ(w^{1/p} x)`, which gives `g ∈ L_q(w μ)`;
then `y = w^{1/q} g`. -/
theorem isDualRep_of_weight (hp : p ≠ ∞) (hq : q ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ))
    {S : Set Z} {w : Z → ℝ≥0} (hw : Measurable w) (hwi : ∫⁻ z, (w z : ℝ≥0∞) ∂μ ≠ ∞)
    (hwS : ∀ z, w z = 0 ↔ z ∉ S) : ∃ y, IsDualRep φ q S y := by
  set ν := μ.withDensity fun z => (w z : ℝ≥0∞) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hwi
  have hp0 : p ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hP : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hP1 : 1 / p.toReal ≠ 0 := one_div_ne_zero hP.ne'
  have hT : ∀ x : Lp ℝ p ν, MemLp (fun z => ((w z ^ (1 / p.toReal) : ℝ≥0) : ℝ) * x z) p μ :=
    fun x => memLp_rpow_mul hw hp0 hp (Lp.stronglyMeasurable x).aestronglyMeasurable (Lp.memLp x)
  let T : Lp ℝ p ν →ₗ[ℝ] Lp ℝ p μ :=
    { toFun := fun x => (hT x).toLp _
      map_add' := fun x x' => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [ae_eq_rpow_mul_of_withDensity hw hP1 (Lp.coeFn_add x x')] with z hz
        simp only [Pi.add_apply] at hz ⊢
        rw [hz, mul_add]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [ae_eq_rpow_mul_of_withDensity hw hP1 (Lp.coeFn_smul c x)] with z hz
        simp only [Pi.smul_apply, smul_eq_mul] at hz ⊢
        rw [hz]; ring }
  have hTn : ∀ x, ‖T x‖ = ‖x‖ := fun x => by
    change ‖(hT x).toLp _‖ = ‖x‖
    rw [Lp.norm_toLp, Lp.norm_def,
      eLpNorm_rpow_mul hw hp0 hp (Lp.stronglyMeasurable x).aestronglyMeasurable]
  let ψ : StrongDual ℝ (Lp ℝ p ν) := (φ.toLinearMap.comp T).mkContinuous ‖φ‖ fun x => by
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [← hTn x]; exact φ.le_opNorm _
  obtain ⟨g, hg, -⟩ := exists_preimage_pairLqLp (μ := ν) hp hq ψ
  refine ⟨fun z => ((w z ^ (1 / q.toReal) : ℝ≥0) : ℝ) * g z,
    memLp_rpow_mul hw hq0 hq (Lp.stronglyMeasurable g).aestronglyMeasurable (Lp.memLp g),
    fun z hz => by simp [(hwS z).2 hz, NNReal.zero_rpow (inv_ne_zero hQ.ne')],
    fun u hu => ?_⟩
  set v := fun z => ((w z ^ (-(1 / p.toReal)) : ℝ≥0) : ℝ) * u z with hvdef
  have hv : MemLp v p ν := memLp_rpow_neg_mul hw hp0 hp (Lp.memLp u)
  have hTv : T (hv.toLp v) = u := by
    change (hT _).toLp _ = u
    conv_rhs => rw [← Lp.toLp_coeFn u (Lp.memLp u)]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [ae_eq_rpow_mul_of_withDensity hw hP1 hv.coeFn_toLp, hu] with z h1 h2
    rw [h1, hvdef]
    dsimp only
    rw [rpow_mul_rpow_neg_mul _ hP1]
    split_ifs with h0
    · exact (h2 ((hwS z).1 h0)).symm
    · rfl
  have key : ∀ z, w z • (g z * v z) =
      ((w z ^ (1 / q.toReal) : ℝ≥0) : ℝ) * g z * u z := fun z => by
    rw [hvdef, NNReal.smul_def, smul_eq_mul]
    by_cases h0 : w z = 0
    · simp [h0, NNReal.zero_rpow (inv_ne_zero hQ.ne')]
    · have e : (w z : ℝ) * ((w z ^ (-(1 / p.toReal)) : ℝ≥0) : ℝ) =
          ((w z ^ (1 / q.toReal) : ℝ≥0) : ℝ) := by
        rw [← NNReal.coe_mul]
        congr 1
        have h1 : w z * w z ^ (-(1 / p.toReal)) = w z ^ (1 + -(1 / p.toReal)) := by
          rw [NNReal.rpow_add h0, NNReal.rpow_one]
        rw [h1]
        congr 1
        have := hPQ.inv_add_inv_eq_one
        rw [one_div, one_div]
        linarith
      calc (w z : ℝ) * (g z * (((w z ^ (-(1 / p.toReal)) : ℝ≥0) : ℝ) * u z)) =
          ((w z : ℝ) * ((w z ^ (-(1 / p.toReal)) : ℝ≥0) : ℝ)) * g z * u z := by ring
        _ = _ := by rw [e]
  calc φ u = ψ (hv.toLp v) := by rw [← hTv]; rfl
    _ = ∫ z, g z * (hv.toLp v) z ∂ν := by rw [← hg, pairLqLp_apply]
    _ = ∫ z, g z * v z ∂ν :=
        integral_congr_ae (by filter_upwards [hv.coeFn_toLp] with z hz; rw [hz])
    _ = ∫ z, w z • (g z * v z) ∂μ := integral_withDensity_eq_integral_smul hw _
    _ = _ := integral_congr_ae (ae_of_all _ fun z => key z)

/-- The test function `t ↦ t |t|^{Q−2}`, that is `sgn(t) |t|^{Q−1}`. -/
noncomputable def testFn (Q t : ℝ) : ℝ := t * |t| ^ (Q - 2)

/-- `t · testFn Q t = |t|^Q`. -/
theorem mul_testFn {Q : ℝ} (hQ : 0 < Q) (t : ℝ) : t * testFn Q t = |t| ^ Q := by
  unfold testFn
  by_cases h : t = 0
  · simp [h, Real.zero_rpow hQ.ne']
  · have ha : 0 < |t| := abs_pos.2 h
    rw [← mul_assoc, ← abs_mul_abs_self t]
    calc |t| * |t| * |t| ^ (Q - 2) = |t| ^ ((1 : ℝ) + 1 + (Q - 2)) := by
          rw [Real.rpow_add ha, Real.rpow_add ha, Real.rpow_one]
      _ = |t| ^ Q := by ring_nf

/-- `|testFn Q t| = |t|^{Q−1}` for `Q > 1`. -/
theorem abs_testFn {Q : ℝ} (hQ : 1 < Q) (t : ℝ) : |testFn Q t| = |t| ^ (Q - 1) := by
  unfold testFn
  by_cases h : t = 0
  · simp [h, Real.zero_rpow (by linarith : Q - 1 ≠ 0)]
  · have ha : 0 < |t| := abs_pos.2 h
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
    calc |t| * |t| ^ (Q - 2) = |t| ^ ((1 : ℝ) + (Q - 2)) := by
          rw [Real.rpow_add ha, Real.rpow_one]
      _ = |t| ^ (Q - 1) := by ring_nf

/-- `testFn Q` is measurable. -/
theorem measurable_testFn (Q : ℝ) : Measurable (testFn Q) :=
  measurable_id.mul (continuous_abs.measurable.pow_const _)

/-- For `d ∈ L_q`, the test function `sgn(d) |d|^{q−1}` lies in `L_p`. -/
theorem memLp_testFn (hp : p ≠ ∞) (hq : q ≠ ∞) {d : Z → ℝ} (hd : MemLp d q μ) :
    MemLp (fun z => testFn q.toReal (d z)) p μ := by
  have hp0 : p ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hm : AEStronglyMeasurable (fun z => testFn q.toReal (d z)) μ :=
    ((measurable_testFn _).comp_aemeasurable
      hd.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hm hp0 hp]
  refine ((integrable_norm_rpow_iff hd.aestronglyMeasurable hq0 hq).2 hd).congr
    (ae_of_all _ fun z => ?_)
  dsimp only
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_testFn (by linarith [hPQ.symm.sub_one_pos]),
    ← Real.rpow_mul (abs_nonneg _), hPQ.symm.sub_one_mul_conj]

/-- `‖sgn(d)|d|^{q−1}‖_p = (∫ |d|^q)^{1/p}`. -/
theorem norm_toLp_testFn (hp : p ≠ ∞) (hq : q ≠ ∞) {d : Z → ℝ} (hd : MemLp d q μ) :
    ‖(memLp_testFn hp hq hd).toLp _‖ = (∫ z, ‖d z‖ ^ q.toReal ∂μ) ^ (1 / p.toReal) := by
  have hp0 : p ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p))
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  rw [Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm hp0 hp (memLp_testFn hp hq hd),
    ENNReal.toReal_ofReal (by positivity), one_div]
  congr 2
  ext z
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_testFn (by linarith [hPQ.symm.sub_one_pos]),
    ← Real.rpow_mul (abs_nonneg _), hPQ.symm.sub_one_mul_conj]

/-- A representing function has `∫ |y|^q ≤ ‖φ‖^q`: test `φ` with `sgn(y)|y|^{q−1}`. -/
theorem IsDualRep.integral_le (hp : p ≠ ∞) (hq : q ≠ ∞) {φ : StrongDual ℝ (Lp ℝ p μ)}
    {S : Set Z} {y : Z → ℝ} (h : IsDualRep φ q S y) :
    ∫ z, ‖y z‖ ^ q.toReal ∂μ ≤ ‖φ‖ ^ q.toReal := by
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  set u := (memLp_testFn hp hq h.1).toLp _
  have hu : ∀ᵐ z ∂μ, z ∉ S → u z = 0 := by
    filter_upwards [MemLp.coeFn_toLp (memLp_testFn hp hq h.1)] with z hz hzS
    rw [hz, h.2.1 z hzS]
    simp [testFn]
  have h1 : φ u = ∫ z, ‖y z‖ ^ q.toReal ∂μ := by
    rw [h.2.2 u hu]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_testFn hp hq h.1)] with z hz
    rw [hz, mul_testFn hQ, Real.norm_eq_abs]
  refine le_rpow_of_le_mul_rpow hPQ (integral_nonneg fun z => by positivity) (norm_nonneg _) ?_
  calc ∫ z, ‖y z‖ ^ q.toReal ∂μ = φ u := h1.symm
    _ ≤ ‖φ‖ * ‖u‖ := (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact φ.le_opNorm u)
    _ = _ := by rw [norm_toLp_testFn hp hq h.1]

/-- A representing function has `‖y‖_q ≤ ‖φ‖`. -/
theorem IsDualRep.eLpNorm_le (hp : p ≠ ∞) (hq : q ≠ ∞) {φ : StrongDual ℝ (Lp ℝ p μ)}
    {S : Set Z} {y : Z → ℝ} (h : IsDualRep φ q S y) :
    eLpNorm y q μ ≤ ENNReal.ofReal ‖φ‖ := by
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [MemLp.eLpNorm_eq_integral_rpow_norm hq0 hq h.1]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (∫ z, ‖y z‖ ^ q.toReal ∂μ) ^ q.toReal⁻¹ ≤ (‖φ‖ ^ q.toReal) ^ q.toReal⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun z => by positivity) (h.integral_le hp hq)
          (inv_nonneg.2 hQ.le)
    _ = ‖φ‖ := by rw [← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hQ.ne', Real.rpow_one]

/-- For every measure and `1 < p < ∞`, `y ↦ (x ↦ ∫ y x dμ)` preserves norms. -/
theorem norm_pairLqLp_eq (hp : p ≠ ∞) (hq : q ≠ ∞) (y : Lp ℝ q μ) :
    ‖pairLqLp μ p q y‖ = ‖y‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
    rw [Real.norm_eq_abs]; exact abs_pairLqLp_le y x) ?_
  have h : IsDualRep (pairLqLp μ p q y) q univ y :=
    ⟨Lp.memLp y, fun z hz => absurd (mem_univ z) hz, fun u _ => pairLqLp_apply y u⟩
  rw [Lp.norm_def]
  exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) (h.eLpNorm_le hp hq)

/-- For every measure and `1 < p < ∞`, `y ↦ (x ↦ ∫ y x dμ)` is injective. -/
theorem pairLqLp_injective_of_ne_top (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Function.Injective (pairLqLp μ p q) := by
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  have h := norm_pairLqLp_eq hp hq y
  rw [hy, norm_zero] at h
  exact norm_eq_zero.1 h.symm

/-- For a σ-finite measure and `1 < p < ∞`, every `φ ∈ L_p*` is `x ↦ ∫ y x dμ` for some
`y ∈ L_q`. The weight is a positive integrable `w` (`exists_pos_lintegral_lt_of_sigmaFinite`). -/
theorem exists_preimage_pairLqLp_sigmaFinite [SigmaFinite μ] (hp : p ≠ ∞) (hq : q ≠ ∞)
    (φ : StrongDual ℝ (Lp ℝ p μ)) : ∃ y : Lp ℝ q μ, pairLqLp μ p q y = φ := by
  obtain ⟨w, hpos, hwm, hwi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  obtain ⟨y, hy⟩ := isDualRep_of_weight (S := univ) hp hq φ hwm (ne_top_of_lt hwi)
    fun z => by simp [(hpos z).ne']
  refine ⟨hy.1.toLp y, ContinuousLinearMap.ext fun u => ?_⟩
  rw [pairLqLp_apply, hy.2.2 u (ae_of_all _ fun z hz => absurd (mem_univ z) hz)]
  exact integral_congr_ae (by filter_upwards [hy.1.coeFn_toLp] with z hz; rw [hz])

/-- `L_p* = L_q` for a σ-finite measure and conjugate `1 < p, q < ∞`. -/
noncomputable def dualLpSigmaFinite [SigmaFinite μ] (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ) :=
  LinearIsometryEquiv.ofSurjective ⟨(pairLqLp μ p q).toLinearMap, norm_pairLqLp_eq hp hq⟩
    (exists_preimage_pairLqLp_sigmaFinite hp hq)

/-- **Example 4** (pp. 449–450) for σ-finite measures: for `1 < p < ∞` with `1/p + 1/q = 1`, the
dual of `L_p(Z, 𝒵, μ)` is `L_q(Z, 𝒵, μ)`. Each `y ∈ L_q` gives `x ↦ ∫ y x dμ` in `L_p*`,
every element of `L_p*` arises from exactly one `y`, and norms are preserved. -/
theorem example_15_4_sigmaFinite [SigmaFinite μ] (hp : p ≠ ∞) (hq : q ≠ ∞) :
    ∃ e : Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ), ∀ y x, e y x = ∫ z, y z * x z ∂μ :=
  ⟨dualLpSigmaFinite hp hq, fun y x => pairLqLp_apply y x⟩

/-- Two functions representing `φ` on the same set agree a.e.: test the difference `d` with
`sgn(d)|d|^{q−1}`. -/
theorem IsDualRep.ae_eq (hp : p ≠ ∞) (hq : q ≠ ∞) {φ : StrongDual ℝ (Lp ℝ p μ)} {S : Set Z}
    {y y' : Z → ℝ} (h : IsDualRep φ q S y) (h' : IsDualRep φ q S y') : y =ᵐ[μ] y' := by
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  set d := y - y' with hd_def
  have hd : MemLp d q μ := h.1.sub h'.1
  set u := (memLp_testFn hp hq hd).toLp _
  have hu : ∀ᵐ z ∂μ, z ∉ S → u z = 0 := by
    filter_upwards [MemLp.coeFn_toLp (memLp_testFn hp hq hd)] with z hz hzS
    rw [hz, hd_def, Pi.sub_apply, h.2.1 z hzS, h'.2.1 z hzS]
    simp [testFn]
  have i1 : Integrable (fun z => y z * u z) μ := h.1.integrable_mul (Lp.memLp u)
  have i2 : Integrable (fun z => y' z * u z) μ := h'.1.integrable_mul (Lp.memLp u)
  have e : ∫ z, d z * u z ∂μ = 0 := by
    have : ∫ z, d z * u z ∂μ = ∫ z, y z * u z ∂μ - ∫ z, y' z * u z ∂μ := by
      rw [← integral_sub i1 i2]
      congr 1
      ext z
      rw [hd_def, Pi.sub_apply, sub_mul]
    rw [this, ← h.2.2 u hu, ← h'.2.2 u hu, sub_self]
  have e2 : ∫ z, ‖d z‖ ^ q.toReal ∂μ = 0 := by
    rw [← e]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_testFn hp hq hd)] with z hz
    rw [hz, mul_testFn hQ, Real.norm_eq_abs]
  have hi : Integrable (fun z => ‖d z‖ ^ q.toReal) μ :=
    (integrable_norm_rpow_iff hd.aestronglyMeasurable hq0 hq).2 hd
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun z => by positivity) hi).1 e2] with z hz
  have h0 : ‖d z‖ ^ q.toReal = 0 := hz
  rw [Real.rpow_eq_zero (norm_nonneg _) hQ.ne', norm_eq_zero, hd_def, Pi.sub_apply,
    sub_eq_zero] at h0
  exact h0

omit [Fact (1 ≤ q)] [p.HolderConjugate q] in
/-- A representation on `S'` restricts to one on a measurable `S ⊆ S'`. -/
theorem IsDualRep.indicator {φ : StrongDual ℝ (Lp ℝ p μ)} {S S' : Set Z} {y : Z → ℝ}
    (hS : MeasurableSet S) (hSS : S ⊆ S') (h : IsDualRep φ q S' y) :
    IsDualRep φ q S (S.indicator y) := by
  refine ⟨h.1.indicator hS, fun z hz => indicator_of_notMem hz _, fun u hu => ?_⟩
  rw [h.2.2 u (by filter_upwards [hu] with z hz hz' using hz fun h => hz' (hSS h))]
  refine integral_congr_ae ?_
  filter_upwards [hu] with z hz
  by_cases hzS : z ∈ S
  · rw [indicator_of_mem hzS]
  · rw [indicator_of_notMem hzS, hz hzS, mul_zero, mul_zero]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q] in
/-- A countable union of sets on which `μ` is σ-finite is one too. -/
theorem sigmaFinite_restrict_iUnion {S : ℕ → Set Z} (hS : ∀ n, MeasurableSet (S n))
    (hσ : ∀ n, SigmaFinite (μ.restrict (S n))) : SigmaFinite (μ.restrict (⋃ n, S n)) := by
  set U := ⋃ n, S n
  refine Measure.sigmaFinite_of_countable (S := range (fun nk : ℕ × ℕ =>
      spanningSets (μ.restrict (S nk.1)) nk.2 ∩ S nk.1) ∪ {Uᶜ})
    ((countable_range _).union (countable_singleton _)) ?_ ?_
  · rintro s (⟨⟨n, k⟩, rfl⟩ | hs)
    · calc μ.restrict U (spanningSets (μ.restrict (S n)) k ∩ S n)
          ≤ μ (spanningSets (μ.restrict (S n)) k ∩ S n) := Measure.restrict_le_self _
        _ = μ.restrict (S n) (spanningSets (μ.restrict (S n)) k) :=
          (Measure.restrict_apply (measurableSet_spanningSets _ _)).symm
        _ < ∞ := measure_spanningSets_lt_top _ _
    · rw [mem_singleton_iff.1 hs, Measure.restrict_apply (MeasurableSet.iUnion hS).compl,
        compl_inter_self, measure_empty]
      exact ENNReal.zero_lt_top
  · refine eq_univ_of_forall fun z => ?_
    by_cases hz : z ∈ U
    · obtain ⟨n, hn⟩ := mem_iUnion.1 hz
      have hz' : z ∈ ⋃ k, spanningSets (μ.restrict (S n)) k := by
        rw [iUnion_spanningSets]; exact mem_univ z
      obtain ⟨k, hk⟩ := mem_iUnion.1 hz'
      exact mem_sUnion.2 ⟨_, Or.inl ⟨(n, k), rfl⟩, hk, hn⟩
    · exact mem_sUnion.2 ⟨Uᶜ, Or.inr rfl, hz⟩

/-- Every `φ ∈ L_p*` is represented on each measurable `S` on which `μ` is σ-finite. The weight
is `1_S g` for a positive `g` with `∫_S g < ∞`. -/
theorem exists_isDualRep (hp : p ≠ ∞) (hq : q ≠ ∞) (φ : StrongDual ℝ (Lp ℝ p μ)) {S : Set Z}
    (hS : MeasurableSet S) [SigmaFinite (μ.restrict S)] : ∃ y, IsDualRep φ q S y := by
  obtain ⟨g, hpos, hgm, hgi⟩ := exists_pos_lintegral_lt_of_sigmaFinite (μ.restrict S) one_ne_zero
  refine isDualRep_of_weight hp hq φ (w := S.indicator g) (hgm.indicator hS) ?_ fun z => ?_
  · have e : ∀ z, ((S.indicator g z : ℝ≥0) : ℝ≥0∞) = S.indicator (fun z => (g z : ℝ≥0∞)) z :=
      fun z => by by_cases hz : z ∈ S <;> simp [hz]
    rw [lintegral_congr e, lintegral_indicator hS]
    exact ne_top_of_lt hgi
  · by_cases hz : z ∈ S <;> simp [hz, (hpos z).ne']

omit [Fact (1 ≤ q)] [p.HolderConjugate q] in
/-- Every `u ∈ L_p`, `p < ∞`, vanishes a.e. off a measurable set on which `μ` is σ-finite. -/
theorem exists_sigmaFinite_support (hp : p ≠ ∞) (u : Lp ℝ p μ) :
    ∃ t, MeasurableSet t ∧ SigmaFinite (μ.restrict t) ∧ ∀ᵐ z ∂μ, z ∉ t → u z = 0 := by
  have hp0 : p ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p))
  obtain ⟨t, ht, hu, hσ⟩ := ((Lp.memLp u).aefinStronglyMeasurable hp0 hp).exists_set_sigmaFinite
  exact ⟨t, ht, hσ, by
    filter_upwards [(ae_restrict_iff' ht.compl).1 hu] with z hz hzt using by simpa using hz hzt⟩

/-- For every measure and `1 < p < ∞`, every `φ ∈ L_p*` is `x ↦ ∫ y x dμ` for some `y ∈ L_q`.
Among the representations `y_S` on σ-finite sets `S`, take `S*` (a countable union) with
`∫ |y_{S*}|^q` maximal. For `u ∈ L_p`, enlarge `S*` by the σ-finite support of `u`: maximality
forces the new representation to vanish off `S*`, so it equals `y_{S*}`. -/
theorem exists_preimage_pairLqLp_of_ne_top (hp : p ≠ ∞) (hq : q ≠ ∞)
    (φ : StrongDual ℝ (Lp ℝ p μ)) : ∃ y : Lp ℝ q μ, pairLqLp μ p q y = φ := by
  have hq0 : q ≠ 0 := ne_zero_of_lt (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q))
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  set A : Set ℝ := {r | ∃ S : Set Z, ∃ y : Z → ℝ, MeasurableSet S ∧ SigmaFinite (μ.restrict S) ∧
    IsDualRep φ q S y ∧ r = ∫ z, ‖y z‖ ^ q.toReal ∂μ}
  have hA : A.Nonempty := by
    have : SigmaFinite (μ.restrict (∅ : Set Z)) := by rw [Measure.restrict_empty]; infer_instance
    obtain ⟨y, hy⟩ := exists_isDualRep hp hq φ MeasurableSet.empty
    exact ⟨_, ∅, y, MeasurableSet.empty, this, hy, rfl⟩
  have hAb : BddAbove A :=
    ⟨‖φ‖ ^ q.toReal, by rintro r ⟨S, y, -, -, hy, rfl⟩; exact hy.integral_le hp hq⟩
  have hint : ∀ {v : Z → ℝ}, MemLp v q μ → Integrable (fun z => ‖v z‖ ^ q.toReal) μ :=
    fun hv => (integrable_norm_rpow_iff hv.aestronglyMeasurable hq0 hq).2 hv
  have hpt : ∀ (T : Set Z) (v : Z → ℝ) (z : Z),
      ‖T.indicator v z‖ ^ q.toReal ≤ ‖v z‖ ^ q.toReal := fun T v z => by
    by_cases hz : z ∈ T
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, norm_zero, Real.zero_rpow hQ.ne']; positivity
  obtain ⟨r, -, hr, hrA⟩ := exists_seq_tendsto_sSup hA hAb
  choose S y hSm hSσ hy hry using hrA
  have hUm : MeasurableSet (⋃ n, S n) := MeasurableSet.iUnion hSm
  have : SigmaFinite (μ.restrict (⋃ n, S n)) := sigmaFinite_restrict_iUnion hSm hSσ
  obtain ⟨ys, hys⟩ := exists_isDualRep hp hq φ hUm
  have hle : sSup A ≤ ∫ z, ‖ys z‖ ^ q.toReal ∂μ := by
    refine le_of_tendsto' hr fun n => ?_
    have e := (hys.indicator (hSm n) (subset_iUnion S n)).ae_eq hp hq (hy n)
    have e' : (fun z => ‖(S n).indicator ys z‖ ^ q.toReal) =ᵐ[μ]
        fun z => ‖y n z‖ ^ q.toReal := by
      filter_upwards [e] with z hz; rw [hz]
    rw [hry n, ← integral_congr_ae e']
    exact integral_mono (hint (hys.1.indicator (hSm n))) (hint hys.1) (hpt _ _)
  refine ⟨hys.1.toLp ys, ContinuousLinearMap.ext fun u => ?_⟩
  obtain ⟨t, ht, htσ, hut⟩ := exists_sigmaFinite_support hp u
  have hσ' : SigmaFinite (μ.restrict ((⋃ n, S n) ∪ t)) := inferInstance
  obtain ⟨y', hy'⟩ := exists_isDualRep hp hq φ (hUm.union ht)
  have e1 : (⋃ n, S n).indicator y' =ᵐ[μ] ys :=
    (hy'.indicator hUm subset_union_left).ae_eq hp hq hys
  have hI : ∫ z, ‖y' z‖ ^ q.toReal ∂μ ≤ ∫ z, ‖(⋃ n, S n).indicator y' z‖ ^ q.toReal ∂μ := by
    calc ∫ z, ‖y' z‖ ^ q.toReal ∂μ ≤ sSup A :=
          le_csSup hAb ⟨_, y', hUm.union ht, hσ', hy', rfl⟩
      _ ≤ ∫ z, ‖ys z‖ ^ q.toReal ∂μ := hle
      _ = _ := integral_congr_ae (by filter_upwards [e1] with z hz; rw [hz])
  have hnn : ∀ z, 0 ≤ ‖y' z‖ ^ q.toReal - ‖(⋃ n, S n).indicator y' z‖ ^ q.toReal :=
    fun z => sub_nonneg.2 (hpt _ _ z)
  have hi := (hint hy'.1).sub (hint (hy'.1.indicator hUm))
  have h0 : ∫ z, (‖y' z‖ ^ q.toReal - ‖(⋃ n, S n).indicator y' z‖ ^ q.toReal) ∂μ = 0 :=
    le_antisymm (by rw [integral_sub (hint hy'.1) (hint (hy'.1.indicator hUm))]; linarith)
      (integral_nonneg hnn)
  have e3 : y' =ᵐ[μ] (⋃ n, S n).indicator y' := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg hnn hi).1 h0] with z hz
    by_cases hzU : z ∈ ⋃ n, S n
    · rw [indicator_of_mem hzU]
    · rw [indicator_of_notMem hzU]
      have h1 : ‖y' z‖ ^ q.toReal = 0 := by
        have h2 : ‖y' z‖ ^ q.toReal - ‖(⋃ n, S n).indicator y' z‖ ^ q.toReal = 0 := hz
        rwa [indicator_of_notMem hzU, norm_zero, Real.zero_rpow hQ.ne', sub_zero] at h2
      rwa [Real.rpow_eq_zero (norm_nonneg _) hQ.ne', norm_eq_zero] at h1
  rw [pairLqLp_apply, hy'.2.2 u (by
    filter_upwards [hut] with z hz hz' using hz fun h => hz' (Or.inr h))]
  refine integral_congr_ae ?_
  filter_upwards [hys.1.coeFn_toLp, e1, e3] with z h1 h2 h3
  rw [h1, h3, h2]

/-- `L_p* = L_q` for every measure and conjugate `1 < p, q < ∞`. -/
noncomputable def dualLpOfNeTop (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ) :=
  LinearIsometryEquiv.ofSurjective ⟨(pairLqLp μ p q).toLinearMap, norm_pairLqLp_eq hp hq⟩
    (exists_preimage_pairLqLp_of_ne_top hp hq)

/-- **Example 4** (pp. 449–450) on an arbitrary measure space: for `1 < p < ∞` with
`1/p + 1/q = 1`, the dual of `L_p(Z, 𝒵, μ)` is `L_q(Z, 𝒵, μ)`, with no finiteness or
σ-finiteness assumption on `μ`. Each `y ∈ L_q` gives `x ↦ ∫ y x dμ` in `L_p*`, every element of
`L_p*` arises from exactly one `y`, and norms are preserved. -/
theorem example_15_4_general (hp : p ≠ ∞) (hq : q ≠ ∞) :
    ∃ e : Lp ℝ q μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ p μ), ∀ y x, e y x = ∫ z, y z * x z ∂μ :=
  ⟨dualLpOfNeTop hp hq, fun y x => pairLqLp_apply y x⟩

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Inner product prices on `L∞`: Lemma 15.7

SLP §15.4, pp. 467–468. `(Z, 𝒵, μ)` is a finite measure space (the book: a probability space) and
`S = L∞(Z, 𝒵, μ)` is Mathlib's `Lp ℝ ⊤ μ`.

* `linftyRestrict μ B`: `x ↦ x · 1_B`; `linftyTrunc μ A`: the **truncation over an event**
  `x^A = x · 1_{Z ∖ A}` (p. 468).
* **Lemma 15.7** (`lemma_15_7`, p. 468): every `φ ∈ L∞(μ)*` has a nested decreasing sequence
  `A_n ∈ 𝒵` with `μ(A_n) → 0` and a `ψ ∈ L∞(μ)*` with `ψ(x) = lim_n φ(x^{A_n})` for all `x` and
  `ψ(x) = ∫ p x dμ` for some `p ∈ L¹(μ)`. In addition `‖ψ‖ ≤ ‖φ‖` and `ψ(x^{A_n}) = φ(x^{A_n})`
  for all `n`, so the remainder `φ − ψ` lives on the sets `A_n` (it is the purely finitely
  additive part of `φ`).

The book omits the proof ("follows directly from Theorems 1.22 and 1.24 of Yosida and Hewitt").
The proof here is direct and avoids `L∞* = ba(μ)` and the Yosida–Hewitt decomposition:
1. `W(B) = ‖φ ∘ (· 1_B)‖` (`linftyRestrictNorm`), the variation of `φ` on `B`, is monotone and
   superadditive on disjoint events (`linftyRestrictNorm_add_le`).
2. `s_m = inf {W(Z ∖ A) : μ(A) ≤ 2^{-m}}` increases to `s` (`linftyTailInf`, `linftyTailSup`);
   near-minimisers give nested `A_n` with `μ(A_n) ≤ 2^{-n}` and `s_n ≤ W(Z ∖ A_n) ≤ s + 2^{-n}`
   (`exists_isLinftyTailSeq`).
3. `|φ(x^{A_m}) − φ(x^{A_n})| ≤ ‖x‖ (W(Z ∖ A_m) − W(Z ∖ A_n))`, so `φ(x^{A_n})` is Cauchy and
   `ψ = lim φ(· ^{A_n})` is a continuous linear functional (`IsLinftyTailSeq.limitDual`).
4. If `μ(B) ≤ 2^{-(m+1)}` then `|ψ(x · 1_B)| ≤ ‖x‖ (s − s_m)`
   (`IsLinftyTailSeq.abs_linftyTruncLimit_restrict_le`), so `E ↦ ψ(1_E)` is a countably additive
   signed measure, absolutely continuous with respect to `μ`
   (`IsLinftyTailSeq.limitSignedMeasure`); Radon–Nikodym gives `p`.
5. `ψ` and `x ↦ ∫ p x dμ` agree on indicators, hence everywhere (`linfty_dual_eq_zero`).

**Note.** The statement is correct (as the transcription's NOTE says); it holds for every finite
measure `μ`, not only probability measures. The book treats one good; `Lp ℝ ⊤ μ` is the
one-good space.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open MeasureTheory Filter Topology Set

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}

/-- An element of `L∞(μ)` is bounded a.e. by its norm: `|x(z)| ≤ ‖x‖` for `μ`-a.e. `z`. -/
theorem ae_abs_le_norm_linfty (x : Lp ℝ ⊤ μ) : ∀ᵐ z ∂μ, |x z| ≤ ‖x‖ := by
  filter_upwards [ae_le_eLpNormEssSup (f := (x : Z → ℝ)) (μ := μ)] with z hz
  have hfin : eLpNorm x ⊤ μ ≠ ⊤ := Lp.eLpNorm_ne_top x
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable x)] at hfin
  rw [← Real.norm_eq_abs, Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable x),
    ← toReal_enorm]
  exact ENNReal.toReal_mono hfin hz

/-- Conversely, an a.e. bound `|x(z)| ≤ C` gives `‖x‖_∞ ≤ C` (finite `μ`). -/
theorem norm_linfty_le_of_ae_abs_le [IsFiniteMeasure μ] {x : Lp ℝ ⊤ μ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ z ∂μ, |x z| ≤ C) : ‖x‖ ≤ C := by
  have := Lp.norm_le_of_ae_bound (f := x) hC (by
    filter_upwards [h] with z hz
    rwa [Real.norm_eq_abs])
  simpa using this

/-- The function `x · 1_B` as an element of `L∞(μ)`, for a measurable `B` (an auxiliary form of
`linftyRestrict`). -/
noncomputable def linftyRestrictFn {B : Set Z} (hB : MeasurableSet B) (x : Lp ℝ ⊤ μ) :
    Lp ℝ ⊤ μ :=
  MemLp.toLp (B.indicator (x : Z → ℝ)) ((Lp.memLp x).indicator hB)

/-- `x · 1_B` agrees a.e. with `1_B x`. -/
theorem coeFn_linftyRestrictFn {B : Set Z} (hB : MeasurableSet B) (x : Lp ℝ ⊤ μ) :
    linftyRestrictFn hB x =ᵐ[μ] B.indicator x :=
  MemLp.coeFn_toLp _

/-- Restriction `x ↦ x · 1_B` to a measurable set `B` as a linear map. -/
noncomputable def linftyRestrictLM {B : Set Z} (hB : MeasurableSet B) :
    Lp ℝ ⊤ μ →ₗ[ℝ] Lp ℝ ⊤ μ where
  toFun := linftyRestrictFn hB
  map_add' x y := by
    apply Lp.ext
    filter_upwards [coeFn_linftyRestrictFn hB (x + y), coeFn_linftyRestrictFn hB x,
      coeFn_linftyRestrictFn hB y, Lp.coeFn_add x y,
      Lp.coeFn_add (linftyRestrictFn hB x) (linftyRestrictFn hB y)] with z h1 h2 h3 h4 h5
    rw [h5, Pi.add_apply, h1, h2, h3]
    by_cases hz : z ∈ B
    · simp only [indicator_of_mem hz, h4, Pi.add_apply]
    · simp only [indicator_of_notMem hz, add_zero]
  map_smul' c x := by
    apply Lp.ext
    filter_upwards [coeFn_linftyRestrictFn hB (c • x), coeFn_linftyRestrictFn hB x,
      Lp.coeFn_smul c x, Lp.coeFn_smul c (linftyRestrictFn hB x)] with z h1 h2 h3 h4
    rw [RingHom.id_apply, h4, Pi.smul_apply, h1, h2]
    by_cases hz : z ∈ B
    · simp only [indicator_of_mem hz, h3, Pi.smul_apply]
    · simp only [indicator_of_notMem hz, smul_zero]

/-- Restriction does not increase the `L∞` norm. -/
theorem norm_linftyRestrictFn_le {B : Set Z} (hB : MeasurableSet B) (x : Lp ℝ ⊤ μ) :
    ‖linftyRestrictFn hB x‖ ≤ ‖x‖ := by
  rw [linftyRestrictFn, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top x) (eLpNorm_indicator_le _ hB)

variable (μ) in
/-- **Restriction to an event**: `x ↦ x · 1_B` as a continuous linear map on `L∞(μ)` (for a
non-measurable `B`, the zero map; it is only used for measurable `B`). -/
noncomputable def linftyRestrict (B : Set Z) : Lp ℝ ⊤ μ →L[ℝ] Lp ℝ ⊤ μ := by
  classical
  exact if hB : MeasurableSet B then
    (linftyRestrictLM hB).mkContinuous 1 (fun x => by
      rw [one_mul]
      exact norm_linftyRestrictFn_le hB x)
  else 0

/-- For measurable `B`, `linftyRestrict μ B` is `x ↦ x · 1_B`. -/
theorem linftyRestrict_apply {B : Set Z} (hB : MeasurableSet B) (x : Lp ℝ ⊤ μ) :
    linftyRestrict μ B x = linftyRestrictFn hB x := by
  simp only [linftyRestrict, hB, ↓reduceDIte]
  rfl

/-- For a non-measurable `B`, `linftyRestrict μ B = 0` (a convention). -/
theorem linftyRestrict_of_not_measurable {B : Set Z} (hB : ¬ MeasurableSet B) :
    linftyRestrict μ B = 0 := by
  simp only [linftyRestrict, hB, ↓reduceDIte]

/-- `x · 1_B` agrees a.e. with `1_B x`. -/
theorem coeFn_linftyRestrict {B : Set Z} (hB : MeasurableSet B) (x : Lp ℝ ⊤ μ) :
    linftyRestrict μ B x =ᵐ[μ] B.indicator x := by
  rw [linftyRestrict_apply hB]
  exact coeFn_linftyRestrictFn hB x

/-- `‖x · 1_B‖_∞ ≤ ‖x‖_∞`. -/
theorem norm_linftyRestrict_le (B : Set Z) (x : Lp ℝ ⊤ μ) : ‖linftyRestrict μ B x‖ ≤ ‖x‖ := by
  by_cases hB : MeasurableSet B
  · rw [linftyRestrict_apply hB]
    exact norm_linftyRestrictFn_le hB x
  · simp [linftyRestrict_of_not_measurable hB]

/-- The restriction operator has norm at most `1`. -/
theorem opNorm_linftyRestrict_le (B : Set Z) : ‖linftyRestrict μ B‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact norm_linftyRestrict_le B x

/-- `(x · 1_C) · 1_B = x · 1_{B ∩ C}`. -/
theorem linftyRestrict_linftyRestrict {B C : Set Z} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (x : Lp ℝ ⊤ μ) : linftyRestrict μ B (linftyRestrict μ C x) = linftyRestrict μ (B ∩ C) x := by
  apply Lp.ext
  filter_upwards [coeFn_linftyRestrict hB (linftyRestrict μ C x), coeFn_linftyRestrict hC x,
    coeFn_linftyRestrict (hB.inter hC) x] with z h1 h2 h3
  rw [h1, h3]
  by_cases hzB : z ∈ B
  · by_cases hzC : z ∈ C
    · simp [hzB, hzC, h2]
    · simp [hzB, hzC, h2]
  · simp [hzB]

/-- For disjoint measurable `B`, `C`: `x · 1_{B ∪ C} = x · 1_B + x · 1_C`. -/
theorem linftyRestrict_union {B C : Set Z} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hd : Disjoint B C) (x : Lp ℝ ⊤ μ) :
    linftyRestrict μ (B ∪ C) x = linftyRestrict μ B x + linftyRestrict μ C x := by
  apply Lp.ext
  filter_upwards [coeFn_linftyRestrict (hB.union hC) x, coeFn_linftyRestrict hB x,
    coeFn_linftyRestrict hC x, Lp.coeFn_add (linftyRestrict μ B x) (linftyRestrict μ C x)]
    with z h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3, indicator_union_of_disjoint hd]

/-- `x · 1_Z = x`. -/
theorem linftyRestrict_univ (x : Lp ℝ ⊤ μ) : linftyRestrict μ univ x = x := by
  apply Lp.ext
  filter_upwards [coeFn_linftyRestrict MeasurableSet.univ x] with z h1
  rw [h1, indicator_univ]

/-- Restriction to a `μ`-null set is `0` in `L∞(μ)`. -/
theorem linftyRestrict_of_null {B : Set Z} (hB : MeasurableSet B) (h : μ B = 0)
    (x : Lp ℝ ⊤ μ) : linftyRestrict μ B x = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_linftyRestrict hB x, Lp.coeFn_zero ℝ ⊤ μ,
    measure_eq_zero_iff_ae_notMem.1 h] with z h1 h2 h3
  rw [h1, h2, indicator_of_notMem h3, Pi.zero_apply]

/-- For disjoint `B`, `C`: `‖u · 1_B + v · 1_C‖_∞ ≤ max ‖u‖_∞ ‖v‖_∞`. -/
theorem norm_linftyRestrict_add_le [IsFiniteMeasure μ] {B C : Set Z} (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hd : Disjoint B C) (u v : Lp ℝ ⊤ μ) :
    ‖linftyRestrict μ B u + linftyRestrict μ C v‖ ≤ max ‖u‖ ‖v‖ := by
  refine norm_linfty_le_of_ae_abs_le (le_max_of_le_left (norm_nonneg _)) ?_
  filter_upwards [Lp.coeFn_add (linftyRestrict μ B u) (linftyRestrict μ C v),
    coeFn_linftyRestrict hB u, coeFn_linftyRestrict hC v, ae_abs_le_norm_linfty u,
    ae_abs_le_norm_linfty v] with z h1 h2 h3 h4 h5
  rw [h1, Pi.add_apply, h2, h3]
  by_cases hzB : z ∈ B
  · have hzC : z ∉ C := Set.disjoint_left.1 hd hzB
    simp only [indicator_of_mem hzB, indicator_of_notMem hzC, add_zero]
    exact h4.trans (le_max_left _ _)
  · by_cases hzC : z ∈ C
    · simp only [indicator_of_mem hzC, indicator_of_notMem hzB, zero_add]
      exact h5.trans (le_max_right _ _)
    · simp only [indicator_of_notMem hzB, indicator_of_notMem hzC, add_zero, abs_zero]
      exact le_max_of_le_left (norm_nonneg _)

/-! ### The variation `W(B)` of `φ` on an event `B` -/

/-- `W(B) = ‖φ ∘ (x ↦ x · 1_B)‖`, the norm of `φ` on the functions supported in `B`; it is the
total variation `|ν|(B)` of the finitely additive set function `ν(E) = φ(1_E)`. -/
noncomputable def linftyRestrictNorm (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (B : Set Z) : ℝ :=
  ‖φ.comp (linftyRestrict μ B)‖

/-- `W(B) ≥ 0`. -/
theorem linftyRestrictNorm_nonneg (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (B : Set Z) :
    0 ≤ linftyRestrictNorm φ B :=
  norm_nonneg _

/-- `W(B) ≤ ‖φ‖`. -/
theorem linftyRestrictNorm_le_norm (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (B : Set Z) :
    linftyRestrictNorm φ B ≤ ‖φ‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (opNorm_linftyRestrict_le B))

/-- `|φ(x · 1_B)| ≤ W(B) ‖x‖_∞`. -/
theorem abs_apply_linftyRestrict_le (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (B : Set Z) (x : Lp ℝ ⊤ μ) :
    |φ (linftyRestrict μ B x)| ≤ linftyRestrictNorm φ B * ‖x‖ :=
  (φ.comp (linftyRestrict μ B)).le_opNorm x

/-- `W` is monotone: `B ⊆ C` implies `W(B) ≤ W(C)`. -/
theorem linftyRestrictNorm_mono (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) {B C : Set Z} (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hBC : B ⊆ C) : linftyRestrictNorm φ B ≤ linftyRestrictNorm φ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ (linftyRestrictNorm_nonneg φ C) fun x => ?_
  have h : linftyRestrict μ B x = linftyRestrict μ C (linftyRestrict μ B x) := by
    rw [linftyRestrict_linftyRestrict hC hB, inter_eq_right.2 hBC]
  rw [ContinuousLinearMap.comp_apply, h]
  exact (abs_apply_linftyRestrict_le φ C _).trans
    (mul_le_mul_of_nonneg_left (norm_linftyRestrict_le B x) (linftyRestrictNorm_nonneg φ C))

/-- Sign flip: for a functional `g` and `x`, some `x'` with `‖x'‖ = ‖x‖` has `g(x') = |g(x)|`. -/
theorem linfty_exists_apply_eq_abs (g : StrongDual ℝ (Lp ℝ ⊤ μ)) (x : Lp ℝ ⊤ μ) :
    ∃ x' : Lp ℝ ⊤ μ, ‖x'‖ = ‖x‖ ∧ g x' = |g x| := by
  rcases le_total 0 (g x) with h | h
  · exact ⟨x, rfl, (abs_of_nonneg h).symm⟩
  · exact ⟨-x, norm_neg x, by rw [map_neg, abs_of_nonpos h]⟩

/-- `W` is superadditive on disjoint measurable sets: `W(B) + W(C) ≤ W(B ∪ C)` (in fact `W` is
additive, but only this inequality is needed). -/
theorem linftyRestrictNorm_add_le [IsFiniteMeasure μ] (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) {B C : Set Z}
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hd : Disjoint B C) :
    linftyRestrictNorm φ B + linftyRestrictNorm φ C ≤ linftyRestrictNorm φ (B ∪ C) := by
  have key : ∀ x y : Lp ℝ ⊤ μ, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |φ (linftyRestrict μ B x)| + |φ (linftyRestrict μ C y)| ≤ linftyRestrictNorm φ (B ∪ C) := by
    intro x y hx hy
    obtain ⟨x', hx'n, hx'⟩ := linfty_exists_apply_eq_abs (φ.comp (linftyRestrict μ B)) x
    obtain ⟨y', hy'n, hy'⟩ := linfty_exists_apply_eq_abs (φ.comp (linftyRestrict μ C)) y
    set z := linftyRestrict μ B x' + linftyRestrict μ C y' with hz
    have hzn : ‖z‖ ≤ 1 :=
      (norm_linftyRestrict_add_le hB hC hd x' y').trans (max_le (hx'n ▸ hx) (hy'n ▸ hy))
    have hrz : linftyRestrict μ (B ∪ C) z = z := by
      rw [hz, map_add, linftyRestrict_linftyRestrict (hB.union hC) hB,
        linftyRestrict_linftyRestrict (hB.union hC) hC, union_inter_cancel_left,
        union_inter_cancel_right]
    have h1 := abs_apply_linftyRestrict_le φ (B ∪ C) z
    rw [hrz, hz, map_add] at h1
    simp only [ContinuousLinearMap.comp_apply] at hx' hy'
    rw [hx', hy', ← hz, abs_of_nonneg (by positivity)] at h1
    exact h1.trans (mul_le_of_le_one_right (linftyRestrictNorm_nonneg φ _) hzn)
  have hC' : ∀ y : Lp ℝ ⊤ μ, ‖y‖ = 1 →
      ‖(φ.comp (linftyRestrict μ C)) y‖ ≤
        linftyRestrictNorm φ (B ∪ C) - linftyRestrictNorm φ B := by
    intro y hy
    have hB' : linftyRestrictNorm φ B ≤
        linftyRestrictNorm φ (B ∪ C) - |φ (linftyRestrict μ C y)| := by
      refine ContinuousLinearMap.opNorm_le_of_unit_norm ?_ fun x hx => ?_
      · have := key 0 y (by simp) hy.le
        simp only [map_zero, abs_zero, zero_add] at this
        linarith
      · have := key x y hx.le hy.le
        rw [ContinuousLinearMap.comp_apply, Real.norm_eq_abs]
        linarith
    rw [ContinuousLinearMap.comp_apply, Real.norm_eq_abs]
    linarith
  have := ContinuousLinearMap.opNorm_le_of_unit_norm (by
      have := linftyRestrictNorm_mono φ hB (hB.union hC) subset_union_left
      linarith) hC'
  change linftyRestrictNorm φ C ≤ _ at this
  linarith

/-! ### The tail sequence `A_n` and the limit functional `ψ` -/

variable (μ) in
/-- **Truncation over an event** (p. 468): `x^A = x · 1_{Z ∖ A}`, i.e. `x^A(z) = 0` on `A` and
`x(z)` off `A`. -/
noncomputable def linftyTrunc (A : Set Z) : Lp ℝ ⊤ μ →L[ℝ] Lp ℝ ⊤ μ := linftyRestrict μ Aᶜ

/-- `s_m = inf {W(Z ∖ A) : A ∈ 𝒵, μ(A) ≤ 2^{-m}}`: the least mass `φ` can keep after cutting
away an event of probability at most `2^{-m}`. -/
noncomputable def linftyTailInf (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (m : ℕ) : ℝ :=
  ⨅ A : {A : Set Z // MeasurableSet A ∧ μ A ≤ 2⁻¹ ^ m}, linftyRestrictNorm φ (A : Set Z)ᶜ

/-- `s_m ≤ W(Z ∖ A)` whenever `μ(A) ≤ 2^{-m}`. -/
theorem linftyTailInf_le (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) {m : ℕ} {A : Set Z} (hA : MeasurableSet A)
    (hμA : μ A ≤ 2⁻¹ ^ m) : linftyTailInf φ m ≤ linftyRestrictNorm φ Aᶜ :=
  ciInf_le (f := fun A : {A : Set Z // MeasurableSet A ∧ μ A ≤ 2⁻¹ ^ m} =>
      linftyRestrictNorm φ (A : Set Z)ᶜ)
    ⟨0, by rintro _ ⟨B, rfl⟩; exact linftyRestrictNorm_nonneg φ _⟩ ⟨A, hA, hμA⟩

/-- `s_m ≥ 0`. -/
theorem linftyTailInf_nonneg (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (m : ℕ) : 0 ≤ linftyTailInf φ m := by
  have : Nonempty {A : Set Z // MeasurableSet A ∧ μ A ≤ 2⁻¹ ^ m} :=
    ⟨⟨∅, MeasurableSet.empty, by simp⟩⟩
  exact le_ciInf fun A => linftyRestrictNorm_nonneg φ _

/-- `s_m ≤ ‖φ‖`. -/
theorem linftyTailInf_le_norm (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (m : ℕ) : linftyTailInf φ m ≤ ‖φ‖ :=
  (linftyTailInf_le φ MeasurableSet.empty (by simp)).trans (linftyRestrictNorm_le_norm φ _)

/-- `s_m` is increasing in `m`. -/
theorem linftyTailInf_mono (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) : Monotone (linftyTailInf φ) := by
  intro m m' hmm'
  have : Nonempty {A : Set Z // MeasurableSet A ∧ μ A ≤ 2⁻¹ ^ m'} :=
    ⟨⟨∅, MeasurableSet.empty, by simp⟩⟩
  refine le_ciInf fun A => linftyTailInf_le φ A.2.1 (A.2.2.trans ?_)
  exact pow_le_pow_of_le_one zero_le (by norm_num) hmm'

/-- `s = sup_m s_m = lim_m s_m`, the mass of the countably additive part of `φ`. -/
noncomputable def linftyTailSup (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) : ℝ := ⨆ m, linftyTailInf φ m

/-- The `s_m` are bounded above by `‖φ‖`. -/
theorem bddAbove_linftyTailInf (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) : BddAbove (range (linftyTailInf φ)) :=
  ⟨‖φ‖, by rintro _ ⟨m, rfl⟩; exact linftyTailInf_le_norm φ m⟩

/-- `s_m ≤ s`. -/
theorem linftyTailInf_le_linftyTailSup (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (m : ℕ) :
    linftyTailInf φ m ≤ linftyTailSup φ :=
  le_ciSup (bddAbove_linftyTailInf φ) m

/-- `s_m → s`. -/
theorem tendsto_linftyTailInf (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) :
    Tendsto (linftyTailInf φ) atTop (𝓝 (linftyTailSup φ)) :=
  tendsto_atTop_ciSup (linftyTailInf_mono φ) (bddAbove_linftyTailInf φ)

/-- A **tail sequence** for `φ`: measurable, nested decreasing `A_n` with `μ(A_n) ≤ 2^{-n}` and
`W(Z ∖ A_n) ≤ s + 2^{-n}` (the sets `A_n` of Lemma 15.7). -/
structure IsLinftyTailSeq (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (A : ℕ → Set Z) : Prop where
  measurableSet : ∀ n, MeasurableSet (A n)
  antitone : Antitone A
  measure_le : ∀ n, μ (A n) ≤ 2⁻¹ ^ n
  linftyRestrictNorm_le : ∀ n, linftyRestrictNorm φ (A n)ᶜ ≤ linftyTailSup φ + 2⁻¹ ^ n

/-- Every `φ ∈ L∞(μ)*` has a tail sequence: choose `A'_n` with `μ(A'_n) ≤ 2^{-(n+1)}` and
`W(Z ∖ A'_n) < s_{n+1} + 2^{-n}`, and put `A_n = ⋃_{k ≥ n} A'_k`. -/
theorem exists_isLinftyTailSeq (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) :
    ∃ A : ℕ → Set Z, IsLinftyTailSeq φ A := by
  have hex : ∀ n : ℕ, ∃ B : {A : Set Z // MeasurableSet A ∧ μ A ≤ 2⁻¹ ^ (n + 1)},
      linftyRestrictNorm φ (B : Set Z)ᶜ < linftyTailInf φ (n + 1) + 2⁻¹ ^ n := fun n => by
    have : Nonempty {A : Set Z // MeasurableSet A ∧ μ A ≤ 2⁻¹ ^ (n + 1)} :=
      ⟨⟨∅, MeasurableSet.empty, by simp⟩⟩
    exact exists_lt_of_ciInf_lt (lt_add_of_pos_right _ (pow_pos (by norm_num) n))
  choose B hB using hex
  refine ⟨fun n => ⋃ k, (B (n + k) : Set Z),
    ⟨fun n => MeasurableSet.iUnion fun k => (B (n + k)).2.1, ?_, fun n => ?_, fun n => ?_⟩⟩
  · refine antitone_nat_of_succ_le fun n => iUnion_subset fun k => ?_
    refine subset_iUnion_of_subset (k + 1) ?_
    rw [show n + 1 + k = n + (k + 1) by ring]
  · calc μ (⋃ k, (B (n + k) : Set Z)) ≤ ∑' k, μ (B (n + k)) := measure_iUnion_le _
      _ ≤ ∑' k, (2⁻¹ : ENNReal) ^ (n + k + 1) := ENNReal.tsum_le_tsum fun k => (B (n + k)).2.2
      _ = 2⁻¹ ^ n := by
        simp_rw [pow_add, pow_one]
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.one_sub_inv_two, inv_inv, mul_assoc,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
  · calc linftyRestrictNorm φ (⋃ k, (B (n + k) : Set Z))ᶜ ≤ linftyRestrictNorm φ (B n : Set Z)ᶜ :=
          linftyRestrictNorm_mono φ (MeasurableSet.iUnion fun k => (B (n + k)).2.1).compl
            (B n).2.1.compl (compl_subset_compl.2 (subset_iUnion_of_subset 0 (by simp)))
      _ ≤ linftyTailInf φ (n + 1) + 2⁻¹ ^ n := (hB n).le
      _ ≤ linftyTailSup φ + 2⁻¹ ^ n := by linarith [linftyTailInf_le_linftyTailSup φ (n + 1)]

variable {φ : StrongDual ℝ (Lp ℝ ⊤ μ)} {A : ℕ → Set Z}

/-- Along a tail sequence, `s_n ≤ W(Z ∖ A_n)`. -/
theorem IsLinftyTailSeq.tailInf_le_restrictNorm (hA : IsLinftyTailSeq φ A) (n : ℕ) :
    linftyTailInf φ n ≤ linftyRestrictNorm φ (A n)ᶜ :=
  linftyTailInf_le φ (hA.measurableSet n) (hA.measure_le n)

/-- For `B' ⊆ B`: `x^{B'} − x^B = x · 1_{(Z ∖ B') ∩ B}`. -/
theorem linftyTrunc_sub_linftyTrunc {B B' : Set Z} (hB : MeasurableSet B)
    (hB' : MeasurableSet B') (h : B' ⊆ B) (x : Lp ℝ ⊤ μ) :
    linftyTrunc μ B' x - linftyTrunc μ B x = linftyRestrict μ (B'ᶜ ∩ B) x := by
  have hset : Bᶜ ∪ (B'ᶜ ∩ B) = B'ᶜ := by
    ext z
    simp only [mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · rintro (hz | ⟨hz, -⟩)
      · exact fun hz' => hz (h hz')
      · exact hz
    · intro hz
      by_cases hzB : z ∈ B
      · exact Or.inr ⟨hz, hzB⟩
      · exact Or.inl hzB
  have hd : Disjoint Bᶜ (B'ᶜ ∩ B) := disjoint_left.2 fun z hz hz' => hz hz'.2
  have h2 := linftyRestrict_union hB.compl (hB'.compl.inter hB) hd x
  rw [hset] at h2
  rw [linftyTrunc, linftyTrunc, h2, add_sub_cancel_left]

/-- For `n ≤ m`: `|φ(x^{A_m}) − φ(x^{A_n})| ≤ ‖x‖ (W(Z ∖ A_m) − W(Z ∖ A_n))`. -/
theorem IsLinftyTailSeq.abs_sub_le [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A) {n m : ℕ}
    (hnm : n ≤ m) (x : Lp ℝ ⊤ μ) :
    |φ (linftyTrunc μ (A m) x) - φ (linftyTrunc μ (A n) x)| ≤
      ‖x‖ * (linftyRestrictNorm φ (A m)ᶜ - linftyRestrictNorm φ (A n)ᶜ) := by
  have hsub := hA.antitone hnm
  rw [← map_sub, linftyTrunc_sub_linftyTrunc (hA.measurableSet n) (hA.measurableSet m) hsub]
  have hd : Disjoint (A n)ᶜ ((A m)ᶜ ∩ A n) := disjoint_left.2 fun z hz hz' => hz hz'.2
  have hun : (A n)ᶜ ∪ ((A m)ᶜ ∩ A n) = (A m)ᶜ := by
    rw [union_inter_distrib_left, compl_union_self, inter_univ,
      union_eq_right.2 (compl_subset_compl.2 hsub)]
  have h1 := linftyRestrictNorm_add_le φ (hA.measurableSet n).compl
    ((hA.measurableSet m).compl.inter (hA.measurableSet n)) hd
  rw [hun] at h1
  calc _ ≤ linftyRestrictNorm φ ((A m)ᶜ ∩ A n) * ‖x‖ := abs_apply_linftyRestrict_le φ _ x
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg x)

/-- Along a tail sequence, `n ↦ φ(x^{A_n})` is a Cauchy sequence. -/
theorem IsLinftyTailSeq.cauchySeq [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A) (x : Lp ℝ ⊤ μ) :
    CauchySeq fun n => φ (linftyTrunc μ (A n) x) := by
  refine cauchySeq_of_le_tendsto_0 (fun N => ‖x‖ * (linftyTailSup φ + 2⁻¹ ^ N - linftyTailInf φ N))
    (fun n m N hn hm => ?_) ?_
  · have key : ∀ n m, N ≤ n → n ≤ m → |φ (linftyTrunc μ (A m) x) - φ (linftyTrunc μ (A n) x)|
        ≤ ‖x‖ * (linftyTailSup φ + 2⁻¹ ^ N - linftyTailInf φ N) := by
      intro n m hn hnm
      refine (hA.abs_sub_le hnm x).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg x))
      have h1 := hA.linftyRestrictNorm_le m
      have h2 := hA.tailInf_le_restrictNorm n
      have h3 : (2⁻¹ : ℝ) ^ m ≤ 2⁻¹ ^ N :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (hn.trans hnm)
      have h4 := linftyTailInf_mono φ hn
      linarith
    rw [Real.dist_eq]
    rcases le_total n m with h | h
    · rw [abs_sub_comm]
      exact key n m hn h
    · exact key m n hm h
  · have : Tendsto (fun N : ℕ => ‖x‖ * (linftyTailSup φ + 2⁻¹ ^ N - linftyTailInf φ N)) atTop
        (𝓝 (‖x‖ * (linftyTailSup φ + 0 - linftyTailSup φ))) :=
      ((tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
        (by norm_num))).sub (tendsto_linftyTailInf φ)).const_mul _
    simpa using this

/-- `ψ(x) = lim_n φ(x^{A_n})` (Lemma 15.7; the limit exists along a tail sequence). -/
noncomputable def linftyTruncLimit (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) (A : ℕ → Set Z)
    (x : Lp ℝ ⊤ μ) : ℝ :=
  limUnder atTop fun n => φ (linftyTrunc μ (A n) x)

/-- `φ(x^{A_n}) → ψ(x)` along a tail sequence. -/
theorem IsLinftyTailSeq.tendsto [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A) (x : Lp ℝ ⊤ μ) :
    Tendsto (fun n => φ (linftyTrunc μ (A n) x)) atTop (𝓝 (linftyTruncLimit φ A x)) :=
  (hA.cauchySeq x).tendsto_limUnder

/-- `ψ` as a continuous linear functional, `‖ψ‖ ≤ ‖φ‖`. -/
noncomputable def IsLinftyTailSeq.limitDual [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A) :
    StrongDual ℝ (Lp ℝ ⊤ μ) :=
  LinearMap.mkContinuous
    { toFun := linftyTruncLimit φ A
      map_add' := fun x y => tendsto_nhds_unique (hA.tendsto (x + y))
        (by simpa only [map_add] using (hA.tendsto x).add (hA.tendsto y))
      map_smul' := fun c x => by
        rw [RingHom.id_apply, smul_eq_mul]
        exact tendsto_nhds_unique (hA.tendsto (c • x))
          (by simpa only [map_smul, smul_eq_mul] using (hA.tendsto x).const_mul c) }
    ‖φ‖ fun x => by
      refine le_of_tendsto' (hA.tendsto x).norm fun n => ?_
      exact (φ.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_linftyRestrict_le _ x) (norm_nonneg φ))

/-- `limitDual` evaluates to `ψ(x) = lim_n φ(x^{A_n})`. -/
theorem IsLinftyTailSeq.limitDual_apply [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A)
    (x : Lp ℝ ⊤ μ) :
    hA.limitDual x = linftyTruncLimit φ A x :=
  rfl

/-- `‖ψ‖ ≤ ‖φ‖`. -/
theorem IsLinftyTailSeq.norm_limitDual_le [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A) :
    ‖hA.limitDual‖ ≤ ‖φ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg φ) _

/-- **Uniform absolute continuity of `ψ`**: if `μ(B) ≤ 2^{-(m+1)}` then
`|ψ(x · 1_B)| ≤ ‖x‖ (s − s_m)`, and `s − s_m → 0`. -/
theorem IsLinftyTailSeq.abs_linftyTruncLimit_restrict_le [IsFiniteMeasure μ]
    (hA : IsLinftyTailSeq φ A) {B : Set Z} (hB : MeasurableSet B) {m : ℕ}
    (hμB : μ B ≤ 2⁻¹ ^ (m + 1)) (x : Lp ℝ ⊤ μ) :
    |linftyTruncLimit φ A (linftyRestrict μ B x)| ≤
      ‖x‖ * (linftyTailSup φ - linftyTailInf φ m) := by
  have hlim : Tendsto (fun n : ℕ => ‖x‖ * (linftyTailSup φ + 2⁻¹ ^ n - linftyTailInf φ m)) atTop
      (𝓝 (‖x‖ * (linftyTailSup φ - linftyTailInf φ m))) := by
    have := (((tendsto_const_nhds (x := linftyTailSup φ)).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
        (by norm_num))).sub_const (linftyTailInf φ m)).const_mul ‖x‖
    simpa using this
  refine le_of_tendsto_of_tendsto (hA.tendsto _).abs hlim ?_
  filter_upwards [eventually_ge_atTop (m + 1)] with n hn
  have hAn := hA.measurableSet n
  rw [linftyTrunc, linftyRestrict_linftyRestrict hAn.compl hB]
  have hd : Disjoint ((A n)ᶜ ∩ B) ((A n)ᶜ ∩ Bᶜ) :=
    disjoint_left.2 fun z hz hz' => hz'.2 hz.2
  have h1 := linftyRestrictNorm_add_le φ (hAn.compl.inter hB) (hAn.compl.inter hB.compl) hd
  rw [inter_union_compl] at h1
  have h2 := hA.linftyRestrictNorm_le n
  have hμ : μ (A n ∪ B) ≤ 2⁻¹ ^ m :=
    calc μ (A n ∪ B) ≤ μ (A n) + μ B := measure_union_le _ _
      _ ≤ 2⁻¹ ^ (m + 1) + 2⁻¹ ^ (m + 1) :=
        add_le_add ((hA.measure_le n).trans (pow_le_pow_of_le_one zero_le
          (by norm_num) hn)) hμB
      _ = 2⁻¹ ^ m := by
        rw [← two_mul, pow_succ, mul_comm (2⁻¹ ^ m), ← mul_assoc,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have h3 : linftyTailInf φ m ≤ linftyRestrictNorm φ ((A n)ᶜ ∩ Bᶜ) := by
    rw [← compl_union]
    exact linftyTailInf_le φ (hAn.union hB) hμ
  have h4 : (2⁻¹ : ℝ) ^ n ≥ 0 := by positivity
  calc _ ≤ linftyRestrictNorm φ ((A n)ᶜ ∩ B) * ‖x‖ := abs_apply_linftyRestrict_le φ _ x
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg x)

/-- `ψ(x^{A_n}) = φ(x^{A_n})`: the remainder `φ − ψ` vanishes on every function vanishing on
`A_n` (it is concentrated on the sets `A_n`, i.e. it is purely finitely additive). -/
theorem IsLinftyTailSeq.linftyTruncLimit_linftyTrunc [IsFiniteMeasure μ]
    (hA : IsLinftyTailSeq φ A) (n : ℕ) (x : Lp ℝ ⊤ μ) :
    linftyTruncLimit φ A (linftyTrunc μ (A n) x) = φ (linftyTrunc μ (A n) x) := by
  refine tendsto_nhds_unique (hA.tendsto _) (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [linftyTrunc, linftyTrunc, linftyRestrict_linftyRestrict (hA.measurableSet m).compl
    (hA.measurableSet n).compl, inter_eq_right.2 (compl_subset_compl.2 (hA.antitone hm))]

/-- If `μ(B_N) → 0` then `ψ(x · 1_{B_N}) → 0`. -/
theorem IsLinftyTailSeq.tendsto_linftyTruncLimit_restrict [IsFiniteMeasure μ]
    (hA : IsLinftyTailSeq φ A) {B : ℕ → Set Z} (hB : ∀ N, MeasurableSet (B N))
    (hμ : Tendsto (fun N => μ (B N)) atTop (𝓝 0)) (x : Lp ℝ ⊤ μ) :
    Tendsto (fun N => linftyTruncLimit φ A (linftyRestrict μ (B N) x)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 : Tendsto (fun m => ‖x‖ * (linftyTailSup φ - linftyTailInf φ m)) atTop (𝓝 0) := by
    simpa using ((tendsto_linftyTailInf φ).const_sub (linftyTailSup φ)).const_mul ‖x‖
  obtain ⟨m, hm⟩ := (h1.eventually (gt_mem_nhds hε)).exists
  have h2 : ∀ᶠ N in atTop, μ (B N) ≤ 2⁻¹ ^ (m + 1) :=
    hμ.eventually (ge_mem_nhds (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 h2
  refine ⟨N₀, fun N hN => ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact (hA.abs_linftyTruncLimit_restrict_le (hB N) (hN₀ N hN) x).trans_lt hm

/-! ### `ψ` is an `L¹` density: the signed measure `E ↦ ψ(1_E)` and Radon–Nikodym -/

variable (μ) in
/-- The constant function `1` in `L∞(μ)`. -/
noncomputable def linftyOne : Lp ℝ ⊤ μ := MemLp.toLp (fun _ => (1 : ℝ)) (memLp_top_const 1)

/-- `1` is a.e. the constant `1`. -/
theorem coeFn_linftyOne : linftyOne μ =ᵐ[μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _

/-- `‖1‖_∞ ≤ 1`. -/
theorem norm_linftyOne_le [IsFiniteMeasure μ] : ‖linftyOne μ‖ ≤ 1 :=
  norm_linfty_le_of_ae_abs_le zero_le_one (by
    filter_upwards [coeFn_linftyOne (μ := μ)] with z hz
    simp [hz])

/-- `1 · 1_E` is a.e. the indicator `1_E`. -/
theorem coeFn_linftyRestrict_one {E : Set Z} (hE : MeasurableSet E) :
    linftyRestrict μ E (linftyOne μ) =ᵐ[μ] E.indicator fun _ => (1 : ℝ) := by
  filter_upwards [coeFn_linftyRestrict hE (linftyOne μ), coeFn_linftyOne (μ := μ)] with z h1 h2
  rw [h1]
  by_cases hz : z ∈ E
  · simp [hz, h2]
  · simp [hz]

/-- Finite superadditivity: `Σ_{i<N} W(f_i) ≤ W(⋃_{i<N} f_i)` for disjoint measurable `f_i`. -/
theorem linftyRestrictNorm_sum_le [IsFiniteMeasure μ] (ψ : StrongDual ℝ (Lp ℝ ⊤ μ)) {f : ℕ → Set Z}
    (hf : ∀ i, MeasurableSet (f i)) (hdisj : Pairwise (Function.onFun Disjoint f)) (N : ℕ) :
    ∑ i ∈ Finset.range N, linftyRestrictNorm ψ (f i) ≤
      linftyRestrictNorm ψ (⋃ i ∈ Finset.range N, f i) := by
  induction N with
  | zero => simp [linftyRestrictNorm_nonneg]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    have hd : Disjoint (⋃ i ∈ Finset.range N, f i) (f N) :=
      disjoint_iUnion_left.2 fun i => disjoint_iUnion_left.2 fun hi =>
        hdisj (Finset.mem_range.1 hi).ne
    exact (add_le_add_left ih _).trans
      (linftyRestrictNorm_add_le ψ (Finset.measurableSet_biUnion _ fun i _ => hf i) (hf N) hd)

/-- Finite additivity of restriction: `x · 1_{⋃_{i<N} f_i} = Σ_{i<N} x · 1_{f_i}`. -/
theorem linftyRestrict_sum [IsFiniteMeasure μ] {f : ℕ → Set Z}
    (hf : ∀ i, MeasurableSet (f i)) (hdisj : Pairwise (Function.onFun Disjoint f)) (N : ℕ)
    (x : Lp ℝ ⊤ μ) :
    linftyRestrict μ (⋃ i ∈ Finset.range N, f i) x =
      ∑ i ∈ Finset.range N, linftyRestrict μ (f i) x := by
  induction N with
  | zero => simp [linftyRestrict_of_null MeasurableSet.empty measure_empty]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.range_add_one, Finset.set_biUnion_insert, union_comm]
    have hd : Disjoint (⋃ i ∈ Finset.range N, f i) (f N) :=
      disjoint_iUnion_left.2 fun i => disjoint_iUnion_left.2 fun hi =>
        hdisj (Finset.mem_range.1 hi).ne
    rw [linftyRestrict_union (Finset.measurableSet_biUnion _ fun i _ => hf i) (hf N) hd, ih]

/-- The **countably additive** signed measure `E ↦ ψ(1_E)` (countable additivity from
`tendsto_linftyTruncLimit_restrict`, absolute summability from superadditivity of `W`). -/
noncomputable def IsLinftyTailSeq.limitSignedMeasure [IsFiniteMeasure μ]
    (hA : IsLinftyTailSeq φ A) :
    SignedMeasure Z where
  measureOf' E := hA.limitDual (linftyRestrict μ E (linftyOne μ))
  empty' := by rw [linftyRestrict_of_null MeasurableSet.empty measure_empty, map_zero]
  not_measurable' E hE := by
    rw [linftyRestrict_of_not_measurable hE, zero_apply, map_zero]
  m_iUnion' f hf hdisj := by
    set ψ := hA.limitDual
    have hsum : Summable fun i => ‖ψ (linftyRestrict μ (f i) (linftyOne μ))‖ := by
      refine summable_of_sum_range_le (c := ‖ψ‖) (fun i => norm_nonneg _) fun N => ?_
      calc ∑ i ∈ Finset.range N, ‖ψ (linftyRestrict μ (f i) (linftyOne μ))‖
          ≤ ∑ i ∈ Finset.range N, linftyRestrictNorm ψ (f i) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [Real.norm_eq_abs]
            exact (abs_apply_linftyRestrict_le ψ _ _).trans
              (mul_le_of_le_one_right (linftyRestrictNorm_nonneg ψ _) norm_linftyOne_le)
        _ ≤ linftyRestrictNorm ψ (⋃ i ∈ Finset.range N, f i) :=
            linftyRestrictNorm_sum_le ψ hf hdisj N
        _ ≤ ‖ψ‖ := linftyRestrictNorm_le_norm ψ _
    rw [hasSum_iff_tendsto_nat_of_summable_norm hsum]
    set T : ℕ → Set Z := fun N => (⋃ i, f i) \ ⋃ i ∈ Finset.range N, f i with hT
    have hTm : ∀ N, MeasurableSet (T N) := fun N =>
      (MeasurableSet.iUnion hf).diff (Finset.measurableSet_biUnion _ fun i _ => hf i)
    have hsplit : ∀ N, ψ (linftyRestrict μ (⋃ i, f i) (linftyOne μ)) =
        ∑ i ∈ Finset.range N, ψ (linftyRestrict μ (f i) (linftyOne μ)) +
          ψ (linftyRestrict μ (T N) (linftyOne μ)) := by
      intro N
      have hun : (⋃ i ∈ Finset.range N, f i) ∪ T N = ⋃ i, f i := by
        rw [hT, union_sdiff_self, union_eq_right]
        exact iUnion₂_subset fun i _ => subset_iUnion f i
      have hd : Disjoint (⋃ i ∈ Finset.range N, f i) (T N) := disjoint_sdiff_right
      rw [← hun, linftyRestrict_union (Finset.measurableSet_biUnion _ fun i _ => hf i) (hTm N) hd,
        linftyRestrict_sum hf hdisj, map_add, map_sum]
    have hTanti : Antitone T := by
      intro N M hNM
      refine sdiff_subset_sdiff_right (iUnion₂_subset fun i hi => ?_)
      exact subset_biUnion_of_mem (Finset.mem_range.2 ((Finset.mem_range.1 hi).trans_le hNM))
    have hTinter : (⋂ N, T N) = ∅ := by
      refine eq_empty_of_forall_notMem fun z hz => ?_
      obtain ⟨i, hi⟩ := mem_iUnion.1 (mem_iInter.1 hz 0).1
      exact (mem_iInter.1 hz (i + 1)).2 (mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_self i)) hi)
    have hμT : Tendsto (fun N => μ (T N)) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := μ) (fun N => (hTm N).nullMeasurableSet) hTanti
        ⟨0, measure_ne_top μ _⟩
      rwa [hTinter, measure_empty] at this
    have h0 := (hA.tendsto_linftyTruncLimit_restrict hTm hμT (linftyOne μ))
    have h1 : Tendsto (fun N => ψ (linftyRestrict μ (⋃ i, f i) (linftyOne μ)) -
        ψ (linftyRestrict μ (T N) (linftyOne μ))) atTop
        (𝓝 (ψ (linftyRestrict μ (⋃ i, f i) (linftyOne μ)) - 0)) :=
      tendsto_const_nhds.sub h0
    rw [sub_zero] at h1
    refine h1.congr fun N => ?_
    rw [hsplit N, add_sub_cancel_right]

/-- `limitSignedMeasure E = ψ(1_E)`. -/
theorem IsLinftyTailSeq.limitSignedMeasure_apply [IsFiniteMeasure μ] (hA : IsLinftyTailSeq φ A)
    (E : Set Z) :
    hA.limitSignedMeasure E = hA.limitDual (linftyRestrict μ E (linftyOne μ)) :=
  rfl

/-- `E ↦ ψ(1_E)` is absolutely continuous with respect to `μ`. -/
theorem IsLinftyTailSeq.limitSignedMeasure_absolutelyContinuous [IsFiniteMeasure μ]
    (hA : IsLinftyTailSeq φ A) : hA.limitSignedMeasure ≪ᵥ μ.toENNRealVectorMeasure := by
  intro E hE
  by_cases hm : MeasurableSet E
  · rw [Measure.toENNRealVectorMeasure_apply_measurable hm] at hE
    rw [hA.limitSignedMeasure_apply, linftyRestrict_of_null hm hE, map_zero]
  · rw [hA.limitSignedMeasure_apply, linftyRestrict_of_not_measurable hm,
      zero_apply, map_zero]

/-- The functional `x ↦ ∫ p x dμ` on `L∞(μ)` for `p ∈ L¹(μ)` (Mathlib's `lpPairing`). -/
noncomputable def linftyL1Pairing (p : Z → ℝ) (hp : Integrable p μ) : StrongDual ℝ (Lp ℝ ⊤ μ) :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 1 ⊤ (hp.toL1 p)

/-- `linftyL1Pairing p x = ∫ p(z) x(z) dμ(z)`. -/
theorem linftyL1Pairing_apply (p : Z → ℝ) (hp : Integrable p μ) (x : Lp ℝ ⊤ μ) :
    linftyL1Pairing p hp x = ∫ z, p z * x z ∂μ := by
  rw [linftyL1Pairing, ContinuousLinearMap.lpPairing_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hp.coeFn_toL1] with z hz
  rw [ContinuousLinearMap.mul_apply', hz]

/-- A continuous linear functional on `L∞(μ)` vanishing on every indicator `1_E` is zero
(`x` is uniformly approximated by the step functions `⌊k x⌋ / k`). -/
theorem linfty_dual_eq_zero [IsFiniteMeasure μ] {χ : StrongDual ℝ (Lp ℝ ⊤ μ)}
    (h : ∀ E, MeasurableSet E → χ (linftyRestrict μ E (linftyOne μ)) = 0) : χ = 0 := by
  ext x
  rw [zero_apply]
  have key : ∀ k : ℕ, |χ x| ≤ ‖χ‖ * (1 / ((k : ℝ) + 1)) := by
    intro k
    set c : ℝ := k + 1 with hc
    have hcpos : 0 < c := by positivity
    have hfm : Measurable (x : Z → ℝ) := (Lp.stronglyMeasurable x).measurable
    have hgm : Measurable fun z => ⌊c * x z⌋ := (hfm.const_mul c).floor
    set N : ℕ := ⌈c * ‖x‖⌉₊ + 1 with hN
    set E : ℤ → Set Z := fun j => {z | ⌊c * x z⌋ = j} with hEdef
    have hE : ∀ j, MeasurableSet (E j) := fun j => hgm (measurableSet_singleton j)
    set J : Finset ℤ := Finset.Icc (-(N : ℤ)) N
    set y : Lp ℝ ⊤ μ := ∑ j ∈ J, ((j : ℝ) / c) • linftyRestrict μ (E j) (linftyOne μ) with hy
    have hχy : χ y = 0 := by
      simp only [hy, map_sum, map_smul, h _ (hE _), smul_zero, Finset.sum_const_zero]
    have hall : ∀ᵐ z ∂μ, ∀ j : ℤ, (((j : ℝ) / c) • linftyRestrict μ (E j) (linftyOne μ) :
        Lp ℝ ⊤ μ) z = (j : ℝ) / c * (E j).indicator (fun _ => (1 : ℝ)) z := by
      rw [ae_all_iff]
      intro j
      filter_upwards [Lp.coeFn_smul ((j : ℝ) / c) (linftyRestrict μ (E j) (linftyOne μ)),
        coeFn_linftyRestrict_one (μ := μ) (hE j)] with z h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    have hxy : ‖x - y‖ ≤ 1 / c := by
      refine norm_linfty_le_of_ae_abs_le (by positivity) ?_
      filter_upwards [Lp.coeFn_sub x y, Lp.coeFn_fun_finsetSum J
        (fun j => ((j : ℝ) / c) • linftyRestrict μ (E j) (linftyOne μ)), hall,
        ae_abs_le_norm_linfty x] with z h1 h2 h3 h4
      rw [h1, Pi.sub_apply, hy, h2]
      simp only [h3]
      set j₀ := ⌊c * x z⌋ with hj₀
      have hfl1 : (j₀ : ℝ) ≤ c * x z := Int.floor_le _
      have hfl2 : c * x z < j₀ + 1 := Int.lt_floor_add_one _
      have hab := abs_le.1 h4
      have hcl : c * ‖x‖ ≤ (⌈c * ‖x‖⌉₊ : ℝ) := Nat.le_ceil _
      have hcx1 : c * x z ≤ c * ‖x‖ := mul_le_mul_of_nonneg_left hab.2 hcpos.le
      have hcx2 : -(c * ‖x‖) ≤ c * x z := by nlinarith [hab.1]
      have hmem : j₀ ∈ J := by
        rw [Finset.mem_Icc]
        constructor
        · have : ((-(N : ℤ) : ℤ) : ℝ) < j₀ := by
            rw [hN]
            push_cast
            linarith
          exact_mod_cast this.le
        · have : (j₀ : ℝ) ≤ ((N : ℤ) : ℝ) := by
            rw [hN]
            push_cast
            linarith
          exact_mod_cast this
      rw [Finset.sum_eq_single j₀]
      · have hz : z ∈ E j₀ := by simp [hEdef, hj₀]
        rw [indicator_of_mem hz, mul_one]
        have : x z - j₀ / c = (c * x z - j₀) / c := by field_simp
        rw [this, abs_div, abs_of_pos hcpos, div_le_div_iff_of_pos_right hcpos, abs_le]
        constructor <;> linarith
      · intro j _ hj
        have hz : z ∉ E j := by
          simp only [hEdef, mem_ofPred_eq]
          exact fun hz => hj (hz ▸ hj₀ ▸ rfl)
        rw [indicator_of_notMem hz, mul_zero]
      · intro hj
        exact absurd hmem hj
    calc |χ x| = |χ (x - y)| := by rw [map_sub, hχy, sub_zero]
      _ ≤ ‖χ‖ * ‖x - y‖ := χ.le_opNorm _
      _ ≤ ‖χ‖ * (1 / c) := mul_le_mul_of_nonneg_left hxy (norm_nonneg χ)
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ‖χ‖
  rw [mul_zero] at hlim
  exact abs_nonpos_iff.1 (ge_of_tendsto' hlim key)

/-- **Lemma 15.7** (p. 468). For every continuous linear functional `φ` on `L∞(Z, 𝒵, μ)` there is a
nested decreasing sequence `A_1 ⊇ A_2 ⊇ …` in `𝒵` with `μ(A_n) → 0` and a continuous linear
functional `ψ` with `ψ(x) = lim_n φ(x^{A_n})` for all `x`, and `ψ(x) = ∫ p x dμ` for some
`p ∈ L¹(μ)`. Also `‖ψ‖ ≤ ‖φ‖` and `ψ = φ` on every `x^{A_n}`. Proved directly (the book cites
Yosida–Hewitt), for any finite `μ`. -/
theorem lemma_15_7 [IsFiniteMeasure μ] (φ : StrongDual ℝ (Lp ℝ ⊤ μ)) :
    ∃ A : ℕ → Set Z, (∀ n, MeasurableSet (A n)) ∧ Antitone A ∧
      Tendsto (fun n => μ (A n)) atTop (𝓝 0) ∧
      ∃ ψ : StrongDual ℝ (Lp ℝ ⊤ μ), ‖ψ‖ ≤ ‖φ‖ ∧
        (∀ x, Tendsto (fun n => φ (linftyTrunc μ (A n) x)) atTop (𝓝 (ψ x))) ∧
        (∀ n x, ψ (linftyTrunc μ (A n) x) = φ (linftyTrunc μ (A n) x)) ∧
        ∃ p : Z → ℝ, Integrable p μ ∧ ∀ x, ψ x = ∫ z, p z * x z ∂μ := by
  obtain ⟨A, hA⟩ := exists_isLinftyTailSeq φ
  refine ⟨A, hA.measurableSet, hA.antitone, ?_, hA.limitDual, hA.norm_limitDual_le, hA.tendsto,
    hA.linftyTruncLimit_linftyTrunc, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := 2⁻¹) (by norm_num))
      (fun n => zero_le) hA.measure_le
  · set s := hA.limitSignedMeasure
    set p := s.rnDeriv μ
    have hp : Integrable p μ := SignedMeasure.integrable_rnDeriv s μ
    have hs := SignedMeasure.withDensityᵥ_rnDeriv_eq s μ
      hA.limitSignedMeasure_absolutelyContinuous
    refine ⟨p, hp, fun x => ?_⟩
    have hχ : hA.limitDual - linftyL1Pairing p hp = 0 := by
      refine linfty_dual_eq_zero fun E hE => ?_
      have h1 : s E = ∫ z in E, p z ∂μ := by
        rw [← hs, withDensityᵥ_apply hp hE]
      rw [sub_apply, linftyL1Pairing_apply, sub_eq_zero]
      rw [hA.limitSignedMeasure_apply] at h1
      rw [h1, ← integral_indicator hE]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_linftyRestrict_one (μ := μ) hE] with z hz
      rw [hz]
      by_cases hzE : z ∈ E
      · simp [hzE]
      · simp [hzE]
    have := congrArg (fun χ : StrongDual ℝ (Lp ℝ ⊤ μ) => χ x) hχ
    simp only [sub_apply, zero_apply, sub_eq_zero] at this
    rw [this, linftyL1Pairing_apply]

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Inner product prices on `L∞`: Assumptions 15.8, 15.9, Exercise 15.12 and Theorem 15.8

SLP §15.4, pp. 468–469. The commodity space is `S = L∞(Z, 𝒵, μ)` (`Lp ℝ ⊤ μ`, one good).

* `LinftyNullSeq μ A`: `A_n ↓ 0` (p. 468).
* **Assumptions 15.8, 15.9** (`Assumption15_8`, `Assumption15_9`, p. 468).
* `supportsAllocation_of_limit_bounds`: the argument of Theorem 15.6, stated once for any normed
  space and any limit functional `ν`; it is reused for Theorems 15.8 and 15.9.
* **Theorem 15.8** (`theorem_15_8`, p. 469): the `L¹` part `ψ` of Lemma 15.7 supports a Pareto
  optimum supported by `φ`; `theorem_15_8_inner_product` combines it with Lemma 15.7.
* **Exercise 15.12** (p. 469): expected utility `u(x) = ∫ U(x(z)) dμᵢ(z)`
  (`linftyExpectedUtility`) with `μᵢ ≪ μ`: Assumption 15.3 (`ex_15_12_assumption15_3`) and
  Assumption 15.9 (`ex_15_12_assumption15_9`) hold for every continuous `U`; Assumption 15.2
  holds for concave `U` (`ex_15_12_assumption15_2`; all three: `ex_15_12`) but not in general
  (`ex_15_12_counterexample`).

**Corrections.**
* Exercise 15.12 is false for Assumption 15.2 as stated: `ex_15_12_counterexample`
  (`Z = {0, 1}`, uniform `μ = μᵢ`, `U(c) = c³`, `x = (2, 0)`, `x′ = (0, 1.9)`, `θ = 1/2`), as the
  transcription's NOTE says and the manual concedes. Corrected statement:
  `ex_15_12_assumption15_2` (`U` concave). The 15.3 and 15.9 parts are true as stated, for any
  finite `μᵢ ≪ μ`, and need only continuity of `U`. (The manual's 15.3 step needs uniform
  continuity of `U` on a bounded interval, unstated; its 15.9 step should read
  `μ(⋂ Aₙ) = lim μ(Aₙ) = 0`, hence `μᵢ(⋂ Aₙ) = 0` by `μᵢ ≪ μ`.)
* Theorem 15.8 assumes 15.1–15.5, 15.8, 15.9; only 15.1, 15.2, 15.8 and 15.9 are used. The
  book's proof "parallels exactly that of Theorem 15.6", whose mixing step needs
  quasi-concavity (hence 15.3) when `uᵢ(x̂ᵢ) = uᵢ(x)`. Here mixing is used only when
  `uᵢ(z) = uᵢ(xᵢ⁰) < uᵢ(x̂ᵢ)`, where 15.2 alone suffices (`supportsAllocation_of_limit_bounds`).
* As for Theorem 15.6, Theorem 15.8 needs a strictly preferred point for every consumer, and it
  does not assert `ψ ≠ 0`.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open MeasureTheory Filter Topology Set

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `A_n ↓ 0` (p. 468): `(A_n) ⊆ 𝒵` is nested decreasing with `μ(A_n) → 0`. -/
structure LinftyNullSeq (μ : Measure Z) (A : ℕ → Set Z) : Prop where
  measurableSet : ∀ n, MeasurableSet (A n)
  antitone : Antitone A
  tendsto_measure : Tendsto (fun n => μ (A n)) atTop (𝓝 0)

/-- **Assumption 15.8** (p. 468): if `x ∈ Xᵢ` and `A_n ↓ 0` then `x^{A_n} ∈ Xᵢ` for all large `n`;
likewise for each `Yⱼ`. -/
def Assumption15_8 (μ : Measure Z) (X : ι → Set (Lp ℝ ⊤ μ)) (Y : κ → Set (Lp ℝ ⊤ μ)) : Prop :=
  (∀ i, ∀ x ∈ X i, ∀ A, LinftyNullSeq μ A → ∀ᶠ n in atTop, linftyTrunc μ (A n) x ∈ X i) ∧
    ∀ j, ∀ y ∈ Y j, ∀ A, LinftyNullSeq μ A → ∀ᶠ n in atTop, linftyTrunc μ (A n) y ∈ Y j

/-- **Assumption 15.9** (p. 468): if `x, x′ ∈ Xᵢ`, `uᵢ(x) > uᵢ(x′)` and `A_n ↓ 0` then
`uᵢ(x^{A_n}) > uᵢ(x′)` for all large `n` (`uᵢ` is defined on all of `S`; with Assumption 15.8,
`x^{A_n} ∈ Xᵢ` eventually, which is the book's implicit reading). -/
def Assumption15_9 (μ : Measure Z) (X : ι → Set (Lp ℝ ⊤ μ)) (u : ι → Lp ℝ ⊤ μ → ℝ) : Prop :=
  ∀ i, ∀ x ∈ X i, ∀ x' ∈ X i, u i x' < u i x → ∀ A, LinftyNullSeq μ A →
    ∀ᶠ n in atTop, u i x' < u i (linftyTrunc μ (A n) x)

/-- **The common core of Theorems 15.6, 15.8 and 15.9** (steps 1–3 of the proof of Theorem 15.6).
Let `φ` support the feasible allocation `[(xᵢ), (yⱼ)]` and let `ν ∈ S*` satisfy
`φ(xᵢ) ≤ ν(z)` whenever `z ∈ Xᵢ` is strictly preferred to `xᵢ`, and `ν(w) ≤ φ(yⱼ)` for
`w ∈ Yⱼ`. If every consumer has a strictly preferred point `x̂ᵢ ∈ Xᵢ`, then `ν` also supports
the allocation. Only Assumptions 15.1 and 15.2 are used: for `uᵢ(z) = uᵢ(xᵢ)` the mixture
`θx̂ᵢ + (1 − θ)z` is strictly preferred by 15.2 alone, so no quasi-concavity (15.3) is needed. -/
theorem supportsAllocation_of_limit_bounds {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {X : ι → Set S} {u : ι → S → ℝ} {Y : κ → Set S} {x : ι → S} {y : κ → S}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) (hF : Feasible X Y x y)
    {φ ν : StrongDual ℝ S} (hsat : ∀ i, ∃ xhat ∈ X i, u i (x i) < u i xhat)
    (hX : ∀ i, ∀ z ∈ X i, u i (x i) < u i z → φ (x i) ≤ ν z)
    (hY : ∀ j, ∀ w ∈ Y j, ν w ≤ φ (y j)) : SupportsAllocation X u Y x y ν := by
  have hX' : ∀ i, ∀ z ∈ X i, u i (x i) ≤ u i z → φ (x i) ≤ ν z := by
    intro i z hz hle
    rcases hle.lt_or_eq with hlt | heq
    · exact hX i z hz hlt
    · obtain ⟨xhat, hxhat, hsat'⟩ := hsat i
      have hzx : u i z < u i xhat := by
        rw [← heq]
        exact hsat'
      have hc : Continuous fun θ : ℝ => θ * ν xhat + (1 - θ) * ν z := by fun_prop
      have ht : Tendsto (fun θ : ℝ => θ * ν xhat + (1 - θ) * ν z) (𝓝[>] 0) (𝓝 (ν z)) := by
        have := hc.tendsto 0
        simp only [zero_mul, sub_zero, one_mul, zero_add] at this
        exact this.mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto ht ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with θ hθ
      have hmem : θ • xhat + (1 - θ) • z ∈ X i :=
        h1 i hxhat hz hθ.1.le (by linarith [hθ.2]) (by ring)
      have hlt : u i (x i) < u i (θ • xhat + (1 - θ) • z) := by
        rw [heq]
        exact h2 i xhat hxhat z hz hzx θ hθ.1 hθ.2
      have := hX i _ hmem hlt
      rwa [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
  obtain ⟨hxX, hyY, hsum⟩ := hF
  have hxi : ∀ i, φ (x i) ≤ ν (x i) := fun i => hX' i (x i) (hxX i) le_rfl
  have hyj : ∀ j, ν (y j) ≤ φ (y j) := fun j => hY j (y j) (hyY j)
  have heq : ∑ i, x i = ∑ j, y j := sub_eq_zero.1 hsum
  have e1 := congrArg ν heq
  have e2 := congrArg φ heq
  simp only [map_sum] at e1 e2
  have hA0 : 0 ≤ ∑ i, (ν (x i) - φ (x i)) :=
    Finset.sum_nonneg fun i _ => sub_nonneg.2 (hxi i)
  have hB0 : 0 ≤ ∑ j, (φ (y j) - ν (y j)) :=
    Finset.sum_nonneg fun j _ => sub_nonneg.2 (hyj j)
  have htot : ∑ i, (ν (x i) - φ (x i)) + ∑ j, (φ (y j) - ν (y j)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    linarith
  have hA : ∑ i, (ν (x i) - φ (x i)) = 0 := by linarith
  have hB : ∑ j, (φ (y j) - ν (y j)) = 0 := by linarith
  have hxeq : ∀ i, ν (x i) = φ (x i) := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.2 (hxi i)).1 hA i
      (Finset.mem_univ i)
    linarith
  have hyeq : ∀ j, ν (y j) = φ (y j) := fun j => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sub_nonneg.2 (hyj j)).1 hB j
      (Finset.mem_univ j)
    linarith
  refine ⟨fun i z hz hle => ?_, fun j w hw => ?_⟩
  · rw [hxeq i]
    exact hX' i z hz hle
  · rw [hyeq j]
    exact hY j w hw

/-- **Theorem 15.8** (p. 469). Under Assumptions 15.1, 15.2, 15.8 and 15.9, if `φ ∈ L∞(μ)*` supports
the feasible allocation (conditions (4) and (5)) and every consumer has a strictly preferred
point, then so does any `ψ` with `ψ(x) = lim_n φ(x^{A_n})` along some `A_n ↓ 0` (in particular
the `ψ` of Lemma 15.7). Assumptions 15.3–15.5 are not needed. -/
theorem theorem_15_8 {X : ι → Set (Lp ℝ ⊤ μ)} {u : ι → Lp ℝ ⊤ μ → ℝ} {Y : κ → Set (Lp ℝ ⊤ μ)}
    {x : ι → Lp ℝ ⊤ μ} {y : κ → Lp ℝ ⊤ μ} (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u)
    (h8 : Assumption15_8 μ X Y) (h9 : Assumption15_9 μ X u) (hF : Feasible X Y x y)
    {φ : StrongDual ℝ (Lp ℝ ⊤ μ)} (hφ : SupportsAllocation X u Y x y φ)
    (hsat : ∀ i, ∃ xhat ∈ X i, u i (x i) < u i xhat) {A : ℕ → Set Z} (hA : LinftyNullSeq μ A)
    {ψ : StrongDual ℝ (Lp ℝ ⊤ μ)}
    (hψ : ∀ z, Tendsto (fun n => φ (linftyTrunc μ (A n) z)) atTop (𝓝 (ψ z))) :
    SupportsAllocation X u Y x y ψ := by
  refine supportsAllocation_of_limit_bounds (φ := φ) h1 h2 hF hsat (fun i z hz hlt => ?_)
    (fun j w hw => ?_)
  · refine ge_of_tendsto (hψ z) ?_
    filter_upwards [h8.1 i z hz A hA, h9 i z hz (x i) (hF.1 i) hlt A hA] with n hn1 hn2
    exact hφ.1 i _ hn1 hn2.le
  · refine le_of_tendsto (hψ w) ?_
    filter_upwards [h8.2 j w hw A hA] with n hn
    exact hφ.2 j _ hn

/-- **Theorem 15.8 with Lemma 15.7**: the supporting `φ` can be replaced by a supporting
`ψ(x) = ∫ p x dμ` with `p ∈ L¹(μ)` and `‖ψ‖ ≤ ‖φ‖`. -/
theorem theorem_15_8_inner_product [IsFiniteMeasure μ] {X : ι → Set (Lp ℝ ⊤ μ)}
    {u : ι → Lp ℝ ⊤ μ → ℝ} {Y : κ → Set (Lp ℝ ⊤ μ)} {x : ι → Lp ℝ ⊤ μ} {y : κ → Lp ℝ ⊤ μ}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) (h8 : Assumption15_8 μ X Y)
    (h9 : Assumption15_9 μ X u) (hF : Feasible X Y x y) {φ : StrongDual ℝ (Lp ℝ ⊤ μ)}
    (hφ : SupportsAllocation X u Y x y φ) (hsat : ∀ i, ∃ xhat ∈ X i, u i (x i) < u i xhat) :
    ∃ ψ : StrongDual ℝ (Lp ℝ ⊤ μ), ‖ψ‖ ≤ ‖φ‖ ∧ SupportsAllocation X u Y x y ψ ∧
      ∃ p : Z → ℝ, Integrable p μ ∧ ∀ z, ψ z = ∫ w, p w * z w ∂μ := by
  obtain ⟨A, hAm, hAa, hAt, ψ, hψn, hψ, -, p, hp, hψp⟩ := lemma_15_7 φ
  exact ⟨ψ, hψn, theorem_15_8 h1 h2 h8 h9 hF hφ hsat ⟨hAm, hAa, hAt⟩ hψ, p, hp, hψp⟩

/-! ### Exercise 15.12 -/

/-- Expected utility `u(x) = ∫ U(x(z)) dν(z)` on `L∞(μ)` (Exercise 15.12; `ν = μᵢ`). -/
noncomputable def linftyExpectedUtility (ν : Measure Z) (U : ℝ → ℝ) (x : Lp ℝ ⊤ μ) : ℝ :=
  ∫ z, U (x z) ∂ν

/-- For `ν ≪ μ` and `x ∈ L∞(μ)`: `|x(z)| ≤ ‖x‖` for `ν`-a.e. `z`. -/
theorem ae_abs_le_norm_linfty_of_ac {ν : Measure Z} (hνμ : ν ≪ μ) (x : Lp ℝ ⊤ μ) :
    ∀ᵐ z ∂ν, |x z| ≤ ‖x‖ :=
  hνμ.ae_le (ae_abs_le_norm_linfty x)

/-- A continuous `U : ℝ → ℝ` is bounded on `[−R, R]`. -/
theorem exists_abs_le_of_continuous {U : ℝ → ℝ} (hU : Continuous U) (R : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ c, |c| ≤ R → |U c| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hU.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun c hc =>
    (Real.norm_eq_abs _ ▸ hC c (abs_le.1 hc)).trans (le_max_left _ _)⟩

/-- For continuous `U`, finite `ν ≪ μ` and `x ∈ L∞(μ)`, `U ∘ x` is `ν`-integrable (so expected
utility is well defined on equivalence classes). -/
theorem integrable_comp_linfty {ν : Measure Z} [IsFiniteMeasure ν] (hνμ : ν ≪ μ) {U : ℝ → ℝ}
    (hU : Continuous U) (x : Lp ℝ ⊤ μ) : Integrable (fun z => U (x z)) ν := by
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_continuous hU ‖x‖
  refine Integrable.of_bound
    (hU.comp_stronglyMeasurable (Lp.stronglyMeasurable x)).aestronglyMeasurable M ?_
  filter_upwards [ae_abs_le_norm_linfty_of_ac hνμ x] with z hz
  rw [Real.norm_eq_abs]
  exact hM _ hz

/-- **Exercise 15.12, Assumption 15.3 part**: for continuous `U` and finite `ν ≪ μ`, expected
utility is continuous on `L∞(μ)` (`U` is uniformly continuous on a bounded interval containing
the essential ranges, the step left implicit in the manual). -/
theorem ex_15_12_continuous {ν : Measure Z} [IsFiniteMeasure ν] (hνμ : ν ≪ μ) {U : ℝ → ℝ}
    (hU : Continuous U) : Continuous (linftyExpectedUtility (μ := μ) ν U) := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  set R := ‖x₀‖ + 1 with hR
  have huc := (isCompact_Icc (a := -R) (b := R)).uniformContinuousOn_of_continuous
    hU.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  set r := ν.real univ with hr
  have hr0 : 0 ≤ r := measureReal_nonneg
  set ε' := ε / (r + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδU⟩ := huc ε' hε'0
  refine ⟨min δ 1, by positivity, fun x hx => ?_⟩
  rw [dist_eq_norm] at hx
  have hae : ∀ᵐ z ∂ν, ‖U (x z) - U (x₀ z)‖ ≤ ε' := by
    filter_upwards [hνμ.ae_le (Lp.coeFn_sub x x₀), ae_abs_le_norm_linfty_of_ac hνμ (x - x₀),
      ae_abs_le_norm_linfty_of_ac hνμ x₀] with z h1 h2 h3
    rw [h1, Pi.sub_apply] at h2
    have h4 : |x z| ≤ R := by
      have := abs_sub_abs_le_abs_sub (x z) (x₀ z)
      linarith [min_le_right δ 1]
    have := hδU (x z) (abs_le.1 h4) (x₀ z) (abs_le.1 (by linarith))
      (by rw [Real.dist_eq]; linarith [min_le_left δ 1])
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    exact this.le
  rw [Real.dist_eq, linftyExpectedUtility, linftyExpectedUtility,
    ← integral_sub (integrable_comp_linfty hνμ hU x) (integrable_comp_linfty hνμ hU x₀),
    ← Real.norm_eq_abs]
  calc ‖∫ z, (U (x z) - U (x₀ z)) ∂ν‖ ≤ ε' * r := norm_integral_le_of_norm_le_const hae
    _ < ε := by
      rw [hε', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith

/-- Expected utility is continuous along event truncations: `u(x^{A_n}) → u(x)` when `A_n ↓ 0`
(dominated convergence; `μ(⋂ A_n) = 0`, hence `ν(⋂ A_n) = 0` by absolute continuity). -/
theorem ex_15_12_tendsto {ν : Measure Z} [IsFiniteMeasure ν] (hνμ : ν ≪ μ) {U : ℝ → ℝ}
    (hU : Continuous U) {A : ℕ → Set Z} (hA : LinftyNullSeq μ A) (x : Lp ℝ ⊤ μ) :
    Tendsto (fun n => linftyExpectedUtility ν U (linftyTrunc μ (A n) x)) atTop
      (𝓝 (linftyExpectedUtility ν U x)) := by
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_continuous hU ‖x‖
  refine tendsto_integral_of_dominated_convergence (fun _ => M)
    (fun n => (integrable_comp_linfty hνμ hU _).aestronglyMeasurable) (integrable_const M)
    (fun n => ?_) ?_
  · filter_upwards [ae_abs_le_norm_linfty_of_ac hνμ (linftyTrunc μ (A n) x)] with z hz
    rw [Real.norm_eq_abs]
    exact hM _ (hz.trans (norm_linftyRestrict_le _ x))
  · have hall : ∀ᵐ z ∂ν, ∀ n, linftyTrunc μ (A n) x z = (A n)ᶜ.indicator x z :=
      hνμ.ae_le (ae_all_iff.2 fun n => coeFn_linftyRestrict (hA.measurableSet n).compl x)
    have hμnull : μ (⋂ n, A n) = 0 :=
      le_antisymm (ge_of_tendsto' hA.tendsto_measure fun n => measure_mono (iInter_subset _ n))
        zero_le
    have hnot : ∀ᵐ z ∂ν, z ∉ ⋂ n, A n := measure_eq_zero_iff_ae_notMem.1 (hνμ hμnull)
    filter_upwards [hall, hnot] with z h1 h2
    obtain ⟨N, hN⟩ : ∃ N, z ∉ A N := by simpa only [mem_iInter, not_forall] using h2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [h1 n, indicator_of_mem (show z ∈ (A n)ᶜ from fun h => hN (hA.antitone hn h))]

omit [Fintype ι] in
/-- **Exercise 15.12, Assumption 15.9 part**: expected utilities with continuous `Uᵢ` and finite
`μᵢ ≪ μ` satisfy Assumption 15.9 (on any `Xᵢ`). -/
theorem ex_15_12_assumption15_9 {X : ι → Set (Lp ℝ ⊤ μ)} {ν : ι → Measure Z}
    [∀ i, IsFiniteMeasure (ν i)] (hνμ : ∀ i, ν i ≪ μ) {U : ι → ℝ → ℝ}
    (hU : ∀ i, Continuous (U i)) :
    Assumption15_9 μ X (fun i => linftyExpectedUtility (ν i) (U i)) := by
  intro i x _ x' _ hlt A hA
  exact (ex_15_12_tendsto (hνμ i) (hU i) hA x).eventually (lt_mem_nhds hlt)

omit [Fintype ι] in
/-- **Exercise 15.12, Assumption 15.3 part**: expected utilities with continuous `Uᵢ` and finite
`μᵢ ≪ μ` satisfy Assumption 15.3. -/
theorem ex_15_12_assumption15_3 {X : ι → Set (Lp ℝ ⊤ μ)} {ν : ι → Measure Z}
    [∀ i, IsFiniteMeasure (ν i)] (hνμ : ∀ i, ν i ≪ μ) {U : ι → ℝ → ℝ}
    (hU : ∀ i, Continuous (U i)) :
    Assumption15_3 X (fun i => linftyExpectedUtility (ν i) (U i)) :=
  fun i => (ex_15_12_continuous (hνμ i) (hU i)).continuousOn

/-- For concave `U`, expected utility is concave: `θu(x) + (1 − θ)u(x′) ≤ u(θx + (1 − θ)x′)`. -/
theorem ex_15_12_concave {ν : Measure Z} [IsFiniteMeasure ν] (hνμ : ν ≪ μ) {U : ℝ → ℝ}
    (hU : ConcaveOn ℝ univ U) (hUc : Continuous U) (x x' : Lp ℝ ⊤ μ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) :
    θ * linftyExpectedUtility ν U x + (1 - θ) * linftyExpectedUtility ν U x' ≤
      linftyExpectedUtility ν U (θ • x + (1 - θ) • x') := by
  rw [linftyExpectedUtility, linftyExpectedUtility, linftyExpectedUtility,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_comp_linfty hνμ hUc x).const_mul θ)
      ((integrable_comp_linfty hνμ hUc x').const_mul (1 - θ))]
  refine integral_mono_ae (((integrable_comp_linfty hνμ hUc x).const_mul θ).add
    ((integrable_comp_linfty hνμ hUc x').const_mul (1 - θ))) (integrable_comp_linfty hνμ hUc _) ?_
  filter_upwards [hνμ.ae_le (Lp.coeFn_add (θ • x) ((1 - θ) • x')),
    hνμ.ae_le (Lp.coeFn_smul θ x), hνμ.ae_le (Lp.coeFn_smul (1 - θ) x')] with z h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply]
  have := hU.2 (mem_univ (x z)) (mem_univ (x' z)) hθ0 (show (0 : ℝ) ≤ 1 - θ by linarith)
    (show θ + (1 - θ) = 1 by ring)
  simpa only [smul_eq_mul] using this

omit [Fintype ι] in
/-- **Exercise 15.12, Assumption 15.2 part, corrected**: with each `Uᵢ` concave (and continuous),
expected utility satisfies Assumption 15.2. (False for merely 15.2-satisfying `Uᵢ`:
`ex_15_12_counterexample`.) -/
theorem ex_15_12_assumption15_2 {X : ι → Set (Lp ℝ ⊤ μ)} {ν : ι → Measure Z}
    [∀ i, IsFiniteMeasure (ν i)] (hνμ : ∀ i, ν i ≪ μ) {U : ι → ℝ → ℝ}
    (hU : ∀ i, ConcaveOn ℝ univ (U i)) (hUc : ∀ i, Continuous (U i)) :
    Assumption15_2 X (fun i => linftyExpectedUtility (ν i) (U i)) := by
  intro i z _ z' _ hlt θ hθ0 hθ1
  have := ex_15_12_concave (hνμ i) (hU i) (hUc i) z z' hθ0.le hθ1.le
  nlinarith

open scoped ENNReal

omit [Fintype ι] in
/-- **Exercise 15.12, corrected** (p. 469): if each `Uᵢ` is concave and continuous and each `μᵢ` is
a finite measure with `μᵢ ≪ μ`, then the expected utilities `uᵢ(x) = ∫ Uᵢ ∘ x dμᵢ` satisfy
Assumptions 15.2, 15.3 and 15.9 (on any `Xᵢ`). -/
theorem ex_15_12 {X : ι → Set (Lp ℝ ⊤ μ)} {ν : ι → Measure Z}
    [∀ i, IsFiniteMeasure (ν i)] (hνμ : ∀ i, ν i ≪ μ) {U : ι → ℝ → ℝ}
    (hU : ∀ i, ConcaveOn ℝ univ (U i)) (hUc : ∀ i, Continuous (U i)) :
    Assumption15_2 X (fun i => linftyExpectedUtility (ν i) (U i)) ∧
      Assumption15_3 X (fun i => linftyExpectedUtility (ν i) (U i)) ∧
      Assumption15_9 μ X (fun i => linftyExpectedUtility (ν i) (U i)) :=
  ⟨ex_15_12_assumption15_2 hνμ hU hUc, ex_15_12_assumption15_3 hνμ hUc,
    ex_15_12_assumption15_9 hνμ hUc⟩

/-- The uniform probability measure on `Z = {0, 1}`. -/
noncomputable def finTwoUniform : Measure (Fin 2) := (2⁻¹ : ℝ≥0∞) • Measure.count

/-- `finTwoUniform` is a probability measure. -/
theorem isProbabilityMeasure_finTwoUniform : IsProbabilityMeasure finTwoUniform := by
  constructor
  rw [finTwoUniform, Measure.smul_apply, Measure.count_univ, smul_eq_mul]
  simp [ENNReal.inv_mul_cancel]

/-- Every point of `{0, 1}` has positive mass, so `a.e.` means everywhere. -/
theorem ae_finTwoUniform_iff {p : Fin 2 → Prop} :
    (∀ᵐ z ∂finTwoUniform, p z) ↔ ∀ z, p z := by
  rw [finTwoUniform, Measure.ae_ennreal_smul_measure_eq (by norm_num), Measure.ae_count_iff]

/-- Expected utility on `{0, 1}`: `u(x) = (U(x(0)) + U(x(1))) / 2`. -/
theorem finTwoUniform_expectedUtility (U : ℝ → ℝ) (x : Lp ℝ ⊤ finTwoUniform) :
    linftyExpectedUtility finTwoUniform U x = (U (x 0) + U (x 1)) / 2 := by
  have : IsProbabilityMeasure finTwoUniform := isProbabilityMeasure_finTwoUniform
  rw [linftyExpectedUtility, integral_fintype Integrable.of_finite, Fin.sum_univ_two]
  simp [finTwoUniform, measureReal_def, Measure.smul_apply]
  ring

/-- Every function on `{0, 1}` is in `L∞`. -/
theorem memLp_finTwoUniform (f : Fin 2 → ℝ) : MemLp f ⊤ finTwoUniform := by
  have : IsProbabilityMeasure finTwoUniform := isProbabilityMeasure_finTwoUniform
  exact MemLp.of_discrete

/-- The element `(a, b)` of `L∞({0, 1})`. -/
noncomputable def finTwoVec (a b : ℝ) : Lp ℝ ⊤ finTwoUniform :=
  (memLp_finTwoUniform ![a, b]).toLp ![a, b]

/-- `(a, b)` evaluates to `a` at `0` and `b` at `1`. -/
theorem finTwoVec_apply (a b : ℝ) (z : Fin 2) : finTwoVec a b z = ![a, b] z :=
  ae_finTwoUniform_iff.1 (memLp_finTwoUniform ![a, b]).coeFn_toLp z

/-- **Exercise 15.12 is false for Assumption 15.2** (NOTE p. 469). On `Z = {0, 1}` with the
uniform probability `μ = μᵢ`, `Xᵢ = L∞` satisfies 15.1 and 15.8 and `U(c) = c³` satisfies
Assumptions 15.2 and 15.3 on `ℝ`, but `u(x) = ∫ U ∘ x dμ` violates Assumption 15.2:
`x = (2, 0)`, `x′ = (0, 1.9)`, `u(x) = 4 > u(x′) = 3.4295`, yet `u(x/2 + x′/2) ≈ 0.929`. -/
theorem ex_15_12_counterexample :
    Assumption15_1 (fun _ : Unit => (univ : Set (Lp ℝ ⊤ finTwoUniform))) ∧
    Assumption15_8 finTwoUniform (fun _ : Unit => (univ : Set (Lp ℝ ⊤ finTwoUniform)))
      (fun _ : Unit => (univ : Set (Lp ℝ ⊤ finTwoUniform))) ∧
    Assumption15_2 (fun _ : Unit => (univ : Set ℝ)) (fun _ => fun c : ℝ => c ^ 3) ∧
    Assumption15_3 (fun _ : Unit => (univ : Set ℝ)) (fun _ => fun c : ℝ => c ^ 3) ∧
    ¬ Assumption15_2 (fun _ : Unit => (univ : Set (Lp ℝ ⊤ finTwoUniform)))
      (fun _ => linftyExpectedUtility finTwoUniform fun c : ℝ => c ^ 3) := by
  refine ⟨fun _ => convex_univ, ⟨fun _ _ _ _ _ => Eventually.of_forall fun _ => mem_univ _,
    fun _ _ _ _ _ => Eventually.of_forall fun _ => mem_univ _⟩, ?_,
    fun _ => (continuous_pow 3).continuousOn, ?_⟩
  · intro _ z _ z' _ hlt θ hθ0 hθ1
    have hmono : StrictMono fun c : ℝ => c ^ 3 := Odd.strictMono_pow (by decide)
    have hzz : z' < z := hmono.lt_iff_lt.1 hlt
    exact hmono (by simp only [smul_eq_mul]; nlinarith)
  · intro h
    have key := h () (finTwoVec 2 0) (mem_univ _) (finTwoVec 0 (19 / 10)) (mem_univ _) ?_
      (1 / 2) (by norm_num) (by norm_num)
    · have hmid : ∀ z, ((1 / 2 : ℝ) • finTwoVec 2 0 + (1 - 1 / 2 : ℝ) • finTwoVec 0 (19 / 10) :
          Lp ℝ ⊤ finTwoUniform) z = ![1, 19 / 20] z := by
        have : IsProbabilityMeasure finTwoUniform := isProbabilityMeasure_finTwoUniform
        intro z
        have h1 := ae_finTwoUniform_iff.1 (Lp.coeFn_add ((1 / 2 : ℝ) • finTwoVec 2 0)
          ((1 - 1 / 2 : ℝ) • finTwoVec 0 (19 / 10))) z
        have h2 := ae_finTwoUniform_iff.1 (Lp.coeFn_smul (1 / 2 : ℝ) (finTwoVec 2 0)) z
        have h3 := ae_finTwoUniform_iff.1
          (Lp.coeFn_smul (1 - 1 / 2 : ℝ) (finTwoVec 0 (19 / 10))) z
        rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, finTwoVec_apply,
          finTwoVec_apply]
        fin_cases z <;> norm_num
      simp only [finTwoUniform_expectedUtility, hmid, finTwoVec_apply] at key
      norm_num at key
    · simp only [finTwoUniform_expectedUtility, finTwoVec_apply]
      norm_num

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Inner product prices for time and uncertainty combined: Theorem 15.9

SLP §15.4, pp. 469–473. `(Z^t, 𝒵^t, μ^t)`, `t = 0, 1, …`, are finite measure spaces (the book:
probability spaces), `X_t = L∞(Z^t, 𝒵^t, μ^t)` and `S = X₀ × X₁ × …` with
`‖x‖_s = sup_t ‖x_t‖_∞` (§15.4 (8)); here `S = LinftyTimeState μ`, Mathlib's `lp` space.

* Truncations: `linftyTimeTrunc T` (`x^T`), `linftyPeriodTrunc t A` (`x^{A_t}`, p. 470), and the
  coordinate embeddings `linftyTSSingle t`, with `ψ_t = φ ∘ linftyTSSingle t`
  (`linftyCoordDual`).
* `Assumption15_6_timeState`, `Assumption15_7_timeState`: Assumptions 15.6, 15.7 on this space
  (p. 469); **Assumptions 15.8′, 15.9′** (`Assumption15_8'`, `Assumption15_9'`, p. 470).
* `exists_linftyTimeState_decomposition`: Lemma 15.7 applied to every `ψ_t`, and the series
  `ν(x) = Σ_t ν_t(x_t)` as a continuous linear functional with `‖ν‖ ≤ ‖φ‖`.
* **Theorem 15.9** (`theorem_15_9`, p. 470): `ν` supports every Pareto optimum supported by `φ`
  and has the inner product form (9), `ν(x) = Σ_t ∫ p_t x_t dμ^t` with `p_t ∈ L¹(μ^t)`.

**Corrections and gaps** (the NOTEs to pp. 471–473, all verified).
* Step 2 (p. 471): the book calls `ν(x) = Σ_t ν_t(x_t)` "the continuous linear functional `ν`"
  without showing that the series converges or that `ν` is bounded. Repaired:
  `Σ_{t<N} |ν_t(x_t)| ≤ ‖φ‖ ‖x‖_s` (limit of `sum_abs_linftyCoordDual_le` applied to the event
  truncations of `x`), so the series converges absolutely and `‖ν‖ ≤ ‖φ‖`
  (`linftySumDual`, `exists_linftyTimeState_decomposition`).
* Step 3 (p. 472): "repeated application" of 15.8′ and 15.9′ does not give one index `N(T)`
  that works for all periods `t ≤ T` at once: these assumptions truncate one period along one
  sequence, so applied in turn they give indices `n₀, n₁(n₀), …` that depend on the earlier
  truncations, and the diagonal choice `n₀ = n₁ = … = n` is not justified by the stated
  assumptions. (No model where the common index fails is constructed here; the step is simply
  unproved.) Repaired by induction over periods with iterated limits
  (`linftyTS_consumer_bound`, `linftyTS_firm_bound`), as the NOTE proposes.
* The proof here does not go through the intermediate `ψ` of Theorem 15.6: (4) and (5) for `φ`
  are applied directly to the time-and-event-truncated points, and the final step
  (step 4, p. 473, correct as the NOTE says) is `supportsAllocation_of_limit_bounds`.
* Assumptions 15.3–15.5 are not used; a strictly preferred point is needed for every consumer
  (as in Theorems 15.6 and 15.8), and `ν ≠ 0` is not asserted.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open MeasureTheory Filter Topology Set

variable {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)] {μ : ∀ t, Measure (Ω t)}
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The time–state commodity space (p. 470): `S = X₀ × X₁ × …` with `X_t = L∞(Z^t, 𝒵^t, μ^t)`
and the norm `‖x‖_s = sup_t ‖x_t‖_∞` (§15.4 (8)), as Mathlib's `lp` space with exponent `∞`. -/
abbrev LinftyTimeState (μ : ∀ t, Measure (Ω t)) : Type _ := lp (fun t => Lp ℝ ⊤ (μ t)) ⊤

/-- `‖x_t‖_∞ ≤ ‖x‖_s`. -/
theorem norm_linftyTimeState_apply_le (x : LinftyTimeState μ) (t : ℕ) : ‖x t‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x t

/-- For `‖L‖ ≤ 1`: `‖L(x_t)‖ ≤ ‖x‖_s`. -/
theorem norm_coord_le_of_opNorm_le {t : ℕ} {L : Lp ℝ ⊤ (μ t) →L[ℝ] Lp ℝ ⊤ (μ t)}
    (hL : ‖L‖ ≤ 1) (x : LinftyTimeState μ) : ‖L (x t)‖ ≤ ‖x‖ :=
  (L.le_of_opNorm_le hL (x t)).trans (by rw [one_mul]; exact norm_linftyTimeState_apply_le x t)

/-- The operator acting coordinatewise by `L_t` (each of norm `≤ 1`): `(x_t)_t ↦ (L_t x_t)_t`. -/
noncomputable def linftyCoordMap (L : ∀ t, Lp ℝ ⊤ (μ t) →L[ℝ] Lp ℝ ⊤ (μ t))
    (hL : ∀ t, ‖L t‖ ≤ 1) : LinftyTimeState μ →L[ℝ] LinftyTimeState μ :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun t => L t (x t), memℓp_infty ⟨‖x‖, by
          rintro _ ⟨t, rfl⟩
          exact norm_coord_le_of_opNorm_le (hL t) x⟩⟩
      map_add' := fun x y => lp.ext (funext fun t => by
        change L t ((x + y) t) = L t (x t) + L t (y t)
        rw [lp.coeFn_add, Pi.add_apply, map_add])
      map_smul' := fun c x => lp.ext (funext fun t => by
        change L t ((c • x) t) = c • L t (x t)
        rw [lp.coeFn_smul, Pi.smul_apply, map_smul]) }
    1 fun x => by
      rw [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg x) fun t => norm_coord_le_of_opNorm_le (hL t) x

/-- `linftyCoordMap L x` has coordinates `L_t x_t`. -/
theorem linftyCoordMap_apply (L : ∀ t, Lp ℝ ⊤ (μ t) →L[ℝ] Lp ℝ ⊤ (μ t)) (hL : ∀ t, ‖L t‖ ≤ 1)
    (x : LinftyTimeState μ) (t : ℕ) : linftyCoordMap L hL x t = L t (x t) :=
  rfl

/-- Coordinatewise contractions do not increase the norm of `S`. -/
theorem norm_linftyCoordMap_apply_le (L : ∀ t, Lp ℝ ⊤ (μ t) →L[ℝ] Lp ℝ ⊤ (μ t))
    (hL : ∀ t, ‖L t‖ ≤ 1) (x : LinftyTimeState μ) : ‖linftyCoordMap L hL x‖ ≤ ‖x‖ :=
  lp.norm_le_of_forall_le (norm_nonneg x) fun t => norm_coord_le_of_opNorm_le (hL t) x

/-- The **time truncation** `x^T = (x₀, …, x_T, 0, 0, …)` (p. 463). -/
noncomputable def linftyTimeTrunc (T : ℕ) : LinftyTimeState μ →L[ℝ] LinftyTimeState μ :=
  linftyCoordMap (fun t => if t ≤ T then ContinuousLinearMap.id ℝ _ else 0) fun t => by
    split_ifs
    · exact ContinuousLinearMap.norm_id_le
    · simp

/-- `(x^T)_t = x_t` for `t ≤ T` and `0` for `t > T`. -/
theorem linftyTimeTrunc_apply (T : ℕ) (x : LinftyTimeState μ) (t : ℕ) :
    linftyTimeTrunc T x t = if t ≤ T then x t else 0 := by
  rw [linftyTimeTrunc, linftyCoordMap_apply]
  split_ifs <;> simp

/-- Truncation of every period `t` on an event `B_t ∈ 𝒵^t`: `(x_t^{B_t})_t`. -/
noncomputable def linftyEventTrunc (B : ∀ t, Set (Ω t)) :
    LinftyTimeState μ →L[ℝ] LinftyTimeState μ :=
  linftyCoordMap (fun t => linftyTrunc (μ t) (B t)) fun _ => opNorm_linftyRestrict_le _

/-- `linftyEventTrunc B x` has coordinates `x_t^{B_t}`. -/
theorem linftyEventTrunc_apply (B : ∀ t, Set (Ω t)) (x : LinftyTimeState μ) (t : ℕ) :
    linftyEventTrunc B x t = linftyTrunc (μ t) (B t) (x t) :=
  rfl

/-- The **one-period truncation** `x^{A_{s}} = (x₀, …, x_{s−1}, x_s^{A}, x_{s+1}, …)` of p. 470. -/
noncomputable def linftyPeriodTrunc (s : ℕ) (A : Set (Ω s)) :
    LinftyTimeState μ →L[ℝ] LinftyTimeState μ :=
  linftyEventTrunc (Function.update (fun t => (∅ : Set (Ω t))) s A)

/-- In period `s`, `x^{A_s}` is `x_s^A`. -/
theorem linftyPeriodTrunc_apply_self (s : ℕ) (A : Set (Ω s)) (x : LinftyTimeState μ) :
    linftyPeriodTrunc s A x s = linftyTrunc (μ s) A (x s) := by
  rw [linftyPeriodTrunc, linftyEventTrunc_apply, Function.update_self]

/-- In every other period, `x^{A_s}` agrees with `x`. -/
theorem linftyPeriodTrunc_apply_of_ne {s t : ℕ} (h : t ≠ s) (A : Set (Ω s))
    (x : LinftyTimeState μ) : linftyPeriodTrunc s A x t = x t := by
  rw [linftyPeriodTrunc, linftyEventTrunc_apply, Function.update_of_ne h, linftyTrunc,
    compl_empty, linftyRestrict_univ]

/-- The embedding of `X_t` as the `t`-th coordinate, `a ↦ (0, …, 0, a, 0, …)`. -/
noncomputable def linftyTSSingle (t : ℕ) : Lp ℝ ⊤ (μ t) →L[ℝ] LinftyTimeState μ :=
  (lp.lsingle (E := fun t => Lp ℝ ⊤ (μ t)) (𝕜 := ℝ) ⊤ t).mkContinuous 1 fun a => by
    rw [one_mul]
    exact (lp.norm_single (E := fun t => Lp ℝ ⊤ (μ t)) ENNReal.zero_lt_top t a).le

/-- Coordinates of the embedded `a`. -/
theorem linftyTSSingle_apply (t : ℕ) (a : Lp ℝ ⊤ (μ t)) (s : ℕ) :
    linftyTSSingle t a s = Pi.single (M := fun t => Lp ℝ ⊤ (μ t)) t a s :=
  rfl

/-- `Σ_{t<k} (b_t at coordinate t)` has coordinate `b_s` for `s < k` and `0` otherwise. -/
theorem linftyTSSingle_sum_apply (k : ℕ) (b : ∀ t, Lp ℝ ⊤ (μ t)) (s : ℕ) :
    (∑ t ∈ Finset.range k, linftyTSSingle t (b t) : LinftyTimeState μ) s =
      if s < k then b s else 0 := by
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [linftyTSSingle_apply]
  rw [Finset.sum_pi_single]
  simp [Finset.mem_range]

/-- The period-`t` component `ψ_t = φ ∘ (embedding of X_t)` of `φ ∈ S*` (Lemma 15.5). -/
noncomputable def linftyCoordDual (φ : StrongDual ℝ (LinftyTimeState μ)) (t : ℕ) :
    StrongDual ℝ (Lp ℝ ⊤ (μ t)) :=
  φ.comp (linftyTSSingle t)

/-- `ψ_t(a) = φ(0, …, 0, a, 0, …)`. -/
theorem linftyCoordDual_apply (φ : StrongDual ℝ (LinftyTimeState μ)) (t : ℕ)
    (a : Lp ℝ ⊤ (μ t)) : linftyCoordDual φ t a = φ (linftyTSSingle t a) :=
  rfl

/-- From the proof of Lemma 15.5: `Σ_{t<N} |ψ_t(y_t)| ≤ ‖φ‖ ‖y‖_s`. -/
theorem sum_abs_linftyCoordDual_le (φ : StrongDual ℝ (LinftyTimeState μ))
    (y : LinftyTimeState μ) (N : ℕ) :
    ∑ t ∈ Finset.range N, |linftyCoordDual φ t (y t)| ≤ ‖φ‖ * ‖y‖ := by
  have hs : ∀ t, ∃ b : Lp ℝ ⊤ (μ t), ‖b‖ = ‖y t‖ ∧
      linftyCoordDual φ t b = |linftyCoordDual φ t (y t)| := fun t =>
    linfty_exists_apply_eq_abs _ _
  choose b hbn hb using hs
  have hz : ‖∑ t ∈ Finset.range N, linftyTSSingle t (b t)‖ ≤ ‖y‖ := by
    refine lp.norm_le_of_forall_le (norm_nonneg y) fun s => ?_
    rw [linftyTSSingle_sum_apply]
    split_ifs
    · rw [hbn]
      exact norm_linftyTimeState_apply_le y s
    · rw [norm_zero]
      exact norm_nonneg y
  calc ∑ t ∈ Finset.range N, |linftyCoordDual φ t (y t)|
      = φ (∑ t ∈ Finset.range N, linftyTSSingle t (b t)) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun t _ => (hb t).symm
    _ ≤ ‖φ (∑ t ∈ Finset.range N, linftyTSSingle t (b t))‖ := le_abs_self _
    _ ≤ ‖φ‖ * ‖∑ t ∈ Finset.range N, linftyTSSingle t (b t)‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * ‖y‖ := mul_le_mul_of_nonneg_left hz (norm_nonneg φ)

/-- A uniform bound on the partial sums of `|ν_t(x_t)|` gives summability. -/
theorem summable_abs_of_sum_le {νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t))} {C : ℝ}
    (h : ∀ (x : LinftyTimeState μ) (N : ℕ), ∑ t ∈ Finset.range N, |νt t (x t)| ≤ C * ‖x‖)
    (x : LinftyTimeState μ) : Summable fun t => |νt t (x t)| :=
  summable_of_sum_range_le (fun _ => abs_nonneg _) (h x)

/-- `ν(x) = Σ_t ν_t(x_t)` as a continuous linear functional, given the bound
`Σ_{t<N} |ν_t(x_t)| ≤ C ‖x‖_s` (the step missing from the book's proof of Theorem 15.9). -/
noncomputable def linftySumDual (νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t))) (C : ℝ)
    (h : ∀ (x : LinftyTimeState μ) (N : ℕ), ∑ t ∈ Finset.range N, |νt t (x t)| ≤ C * ‖x‖) :
    StrongDual ℝ (LinftyTimeState μ) :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' t, νt t (x t)
      map_add' := fun x y => by
        simp only [lp.coeFn_add, Pi.add_apply, map_add]
        exact (summable_abs_of_sum_le h x).of_abs.tsum_add (summable_abs_of_sum_le h y).of_abs
      map_smul' := fun c x => by
        simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact tsum_mul_left }
    C fun x => by
      rw [Real.norm_eq_abs]
      calc |∑' t, νt t (x t)| ≤ ∑' t, |νt t (x t)| := by
            simpa only [Real.norm_eq_abs] using
              norm_tsum_le_tsum_norm (f := fun t => νt t (x t)) (by
                simpa only [Real.norm_eq_abs] using summable_abs_of_sum_le h x)
        _ ≤ C * ‖x‖ := Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) (h x)

/-- `ν(x) = Σ_t ν_t(x_t)`, the series converging absolutely. -/
theorem hasSum_linftySumDual (νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t))) (C : ℝ)
    (h : ∀ (x : LinftyTimeState μ) (N : ℕ), ∑ t ∈ Finset.range N, |νt t (x t)| ≤ C * ‖x‖)
    (x : LinftyTimeState μ) : HasSum (fun t => νt t (x t)) (linftySumDual νt C h x) :=
  (summable_abs_of_sum_le h x).of_abs.hasSum

/-- `‖ν‖ ≤ C`. -/
theorem norm_linftySumDual_le (νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t))) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (x : LinftyTimeState μ) (N : ℕ), ∑ t ∈ Finset.range N, |νt t (x t)| ≤ C * ‖x‖) :
    ‖linftySumDual νt C h‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

/-- **Steps 2 and 5 of the proof of Theorem 15.9, with the continuity of `ν` (NOTE p. 471)**:
for `φ ∈ S*` there are `A_{t n} ↓ 0` in each `𝒵^t` and `ν_t ∈ X_t*` with
`ν_t(a) = lim_n ψ_t(a^{A_{t n}})` (Lemma 15.7 applied to each `ψ_t`), `ν_t(a) = ∫ p_t a dμ^t` with
`p_t ∈ L¹(μ^t)`, and `ν(x) = Σ_t ν_t(x_t)` is a continuous linear functional with `‖ν‖ ≤ ‖φ‖`. -/
theorem exists_linftyTimeState_decomposition [∀ t, IsFiniteMeasure (μ t)]
    (φ : StrongDual ℝ (LinftyTimeState μ)) :
    ∃ A : ∀ t, ℕ → Set (Ω t), (∀ t, LinftyNullSeq (μ t) (A t)) ∧
      ∃ νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t)),
        (∀ t a, Tendsto (fun n => linftyCoordDual φ t (linftyTrunc (μ t) (A t n) a)) atTop
          (𝓝 (νt t a))) ∧
        (∀ t, ∃ p : Ω t → ℝ, Integrable p (μ t) ∧ ∀ a, νt t a = ∫ z, p z * a z ∂(μ t)) ∧
        ∃ ν : StrongDual ℝ (LinftyTimeState μ), ‖ν‖ ≤ ‖φ‖ ∧
          ∀ x, HasSum (fun t => νt t (x t)) (ν x) := by
  choose A hAm hAa hAt νt hνn hνlim hνeq p hp hνp using
    fun t => lemma_15_7 (linftyCoordDual φ t)
  have hbound : ∀ (x : LinftyTimeState μ) (N : ℕ),
      ∑ t ∈ Finset.range N, |νt t (x t)| ≤ ‖φ‖ * ‖x‖ := by
    intro x N
    have hlim : Tendsto (fun n => ∑ t ∈ Finset.range N,
        |linftyCoordDual φ t (linftyTrunc (μ t) (A t n) (x t))|) atTop
        (𝓝 (∑ t ∈ Finset.range N, |νt t (x t)|)) :=
      tendsto_finsetSum _ fun t _ => (hνlim t (x t)).abs
    refine le_of_tendsto' hlim fun n => ?_
    have := sum_abs_linftyCoordDual_le φ (linftyEventTrunc (fun t => A t n) x) N
    simp only [linftyEventTrunc_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_left (norm_linftyCoordMap_apply_le _ _ x)
      (norm_nonneg φ))
  exact ⟨A, fun t => ⟨hAm t, hAa t, hAt t⟩, νt, hνlim, fun t => ⟨p t, hp t, hνp t⟩,
    linftySumDual νt ‖φ‖ hbound, norm_linftySumDual_le νt (norm_nonneg φ) hbound,
    hasSum_linftySumDual νt ‖φ‖ hbound⟩

/-- **Assumption 15.6** for the time–state space (p. 465, extended on p. 469): time truncations
of consumption and production plans are feasible far enough out. -/
def Assumption15_6_timeState (X : ι → Set (LinftyTimeState μ)) (Y : κ → Set (LinftyTimeState μ)) :
    Prop :=
  (∀ i, ∀ x ∈ X i, ∀ᶠ T in atTop, linftyTimeTrunc T x ∈ X i) ∧
    ∀ j, ∀ y ∈ Y j, ∀ᶠ T in atTop, linftyTimeTrunc T y ∈ Y j

/-- **Assumption 15.7** for the time–state space (p. 465, extended on p. 469). -/
def Assumption15_7_timeState (X : ι → Set (LinftyTimeState μ))
    (u : ι → LinftyTimeState μ → ℝ) : Prop :=
  ∀ i, ∀ x ∈ X i, ∀ x' ∈ X i, u i x' < u i x → ∀ᶠ T in atTop, u i x' < u i (linftyTimeTrunc T x)

/-- **Assumption 15.8′** (p. 470): for every period `t`, if `x ∈ Xᵢ` and `A_{t n} ↓ 0` in `𝒵^t`
then `x^{A_{t n}} ∈ Xᵢ` for all large `n`; likewise for each `Yⱼ`. -/
def Assumption15_8' (μ : ∀ t, Measure (Ω t)) (X : ι → Set (LinftyTimeState μ))
    (Y : κ → Set (LinftyTimeState μ)) : Prop :=
  (∀ i t, ∀ x ∈ X i, ∀ A : ℕ → Set (Ω t), LinftyNullSeq (μ t) A →
      ∀ᶠ n in atTop, linftyPeriodTrunc t (A n) x ∈ X i) ∧
    ∀ j t, ∀ y ∈ Y j, ∀ A : ℕ → Set (Ω t), LinftyNullSeq (μ t) A →
      ∀ᶠ n in atTop, linftyPeriodTrunc t (A n) y ∈ Y j

/-- **Assumption 15.9′** (p. 470): for every period `t`, if `x, x′ ∈ Xᵢ`, `uᵢ(x) > uᵢ(x′)` and
`A_{t n} ↓ 0` then `uᵢ(x^{A_{t n}}) > uᵢ(x′)` for all large `n`. -/
def Assumption15_9' (μ : ∀ t, Measure (Ω t)) (X : ι → Set (LinftyTimeState μ))
    (u : ι → LinftyTimeState μ → ℝ) : Prop :=
  ∀ i t, ∀ x ∈ X i, ∀ x' ∈ X i, u i x' < u i x → ∀ A : ℕ → Set (Ω t), LinftyNullSeq (μ t) A →
    ∀ᶠ n in atTop, u i x' < u i (linftyPeriodTrunc t (A n) x)

/-- Bookkeeping for the iterated limits: with the first `k` periods removed, the period-`k`
truncation of `w` is `w` with the first `k + 1` periods removed plus `w_k^B` in period `k`. -/
theorem linftyPeriodTrunc_drop (k : ℕ) (B : Set (Ω k)) (w : LinftyTimeState μ) :
    linftyPeriodTrunc k B w -
        ∑ t ∈ Finset.range k, linftyTSSingle t (linftyPeriodTrunc k B w t) =
      (w - ∑ t ∈ Finset.range (k + 1), linftyTSSingle t (w t)) +
        linftyTSSingle k (linftyTrunc (μ k) B (w k)) := by
  refine lp.ext (funext fun s => ?_)
  rw [lp.coeFn_sub, lp.coeFn_add, lp.coeFn_sub, Pi.sub_apply, Pi.add_apply, Pi.sub_apply,
    linftyTSSingle_sum_apply, linftyTSSingle_sum_apply, linftyTSSingle_apply]
  rcases lt_trichotomy s k with h | rfl | h
  · have h' : s < k + 1 := by omega
    simp only [h, h', ↓reduceIte, Pi.single_eq_of_ne h.ne, linftyPeriodTrunc_apply_of_ne h.ne]
    simp
  · simp only [lt_self_iff_false, Nat.lt_succ_self, ↓reduceIte, Pi.single_eq_same,
      linftyPeriodTrunc_apply_self]
    simp
  · have h1 : ¬ s < k := by omega
    have h2 : ¬ s < k + 1 := by omega
    simp only [h1, h2, ↓reduceIte, Pi.single_eq_of_ne h.ne', linftyPeriodTrunc_apply_of_ne h.ne']
    simp

/-- `x^T` with its first `T + 1` periods removed is `0`. -/
theorem linftyTimeTrunc_drop (T : ℕ) (w : LinftyTimeState μ) :
    linftyTimeTrunc T w - ∑ t ∈ Finset.range (T + 1), linftyTSSingle t (linftyTimeTrunc T w t) =
      0 := by
  refine lp.ext (funext fun s => ?_)
  rw [lp.coeFn_sub, Pi.sub_apply, linftyTSSingle_sum_apply, lp.coeFn_zero, Pi.zero_apply]
  by_cases h : s < T + 1
  · simp only [h, ↓reduceIte, sub_self]
  · simp only [h, ↓reduceIte, linftyTimeTrunc_apply, show ¬ s ≤ T by omega, sub_zero]

omit [Fintype ι] [Fintype κ] in
/-- **Step 3, (13), by iterated limits** (the repair of the NOTE to p. 472). If `z ∈ Xᵢ` with
`uᵢ(z) > uᵢ(x⁰)` then `φ(x⁰) ≤ Σ_{t<k} ν_t(z_t) + φ(z with periods < k removed)`: truncate
period `k − 1` (15.8′, 15.9′), apply the case `k − 1` to the truncated point, and let the
period-`k − 1` index tend to infinity. No common truncation index is needed. -/
theorem linftyTS_consumer_bound {X : ι → Set (LinftyTimeState μ)}
    {Y : κ → Set (LinftyTimeState μ)} {u : ι → LinftyTimeState μ → ℝ}
    (h8 : Assumption15_8' μ X Y) (h9 : Assumption15_9' μ X u)
    {φ : StrongDual ℝ (LinftyTimeState μ)} {i : ι} {x0 : LinftyTimeState μ} (hx0 : x0 ∈ X i)
    (hφ : ∀ z ∈ X i, u i x0 ≤ u i z → φ x0 ≤ φ z)
    {A : ∀ t, ℕ → Set (Ω t)} (hA : ∀ t, LinftyNullSeq (μ t) (A t))
    {νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t))}
    (hν : ∀ t a, Tendsto (fun n => linftyCoordDual φ t (linftyTrunc (μ t) (A t n) a)) atTop
      (𝓝 (νt t a))) (k : ℕ) :
    ∀ w ∈ X i, u i x0 < u i w → φ x0 ≤ ∑ t ∈ Finset.range k, νt t (w t) +
      φ (w - ∑ t ∈ Finset.range k, linftyTSSingle t (w t)) := by
  induction k with
  | zero =>
    intro w hw hlt
    simpa using hφ w hw hlt.le
  | succ k ih =>
    intro w hw hlt
    have hev : ∀ᶠ n in atTop, φ x0 ≤ ∑ t ∈ Finset.range k, νt t (w t) +
        (φ (w - ∑ t ∈ Finset.range (k + 1), linftyTSSingle t (w t)) +
          linftyCoordDual φ k (linftyTrunc (μ k) (A k n) (w k))) := by
      filter_upwards [h8.1 i k w hw (A k) (hA k), h9 i k w hw x0 hx0 hlt (A k) (hA k)]
        with n hn1 hn2
      have h := ih _ hn1 hn2
      rw [linftyPeriodTrunc_drop, map_add, ← linftyCoordDual_apply] at h
      rwa [Finset.sum_congr rfl fun t ht => by
        rw [linftyPeriodTrunc_apply_of_ne (Finset.mem_range.1 ht).ne]] at h
    have hlim := (tendsto_const_nhds (x := ∑ t ∈ Finset.range k, νt t (w t))).add
      ((tendsto_const_nhds (x := φ (w - ∑ t ∈ Finset.range (k + 1),
        linftyTSSingle t (w t)))).add (hν k (w k)))
    have := ge_of_tendsto hlim hev
    rw [Finset.sum_range_succ]
    linarith

omit [Fintype ι] [Fintype κ] in
/-- **Step 3, (14), by iterated limits**: for `w ∈ Yⱼ`,
`Σ_{t<k} ν_t(w_t) + φ(w with periods < k removed) ≤ φ(y⁰)`. -/
theorem linftyTS_firm_bound {X : ι → Set (LinftyTimeState μ)}
    {Y : κ → Set (LinftyTimeState μ)} (h8 : Assumption15_8' μ X Y)
    {φ : StrongDual ℝ (LinftyTimeState μ)} {j : κ} {y0 : LinftyTimeState μ}
    (hφ : ∀ w ∈ Y j, φ w ≤ φ y0)
    {A : ∀ t, ℕ → Set (Ω t)} (hA : ∀ t, LinftyNullSeq (μ t) (A t))
    {νt : ∀ t, StrongDual ℝ (Lp ℝ ⊤ (μ t))}
    (hν : ∀ t a, Tendsto (fun n => linftyCoordDual φ t (linftyTrunc (μ t) (A t n) a)) atTop
      (𝓝 (νt t a))) (k : ℕ) :
    ∀ w ∈ Y j, ∑ t ∈ Finset.range k, νt t (w t) +
      φ (w - ∑ t ∈ Finset.range k, linftyTSSingle t (w t)) ≤ φ y0 := by
  induction k with
  | zero =>
    intro w hw
    simpa using hφ w hw
  | succ k ih =>
    intro w hw
    have hev : ∀ᶠ n in atTop, ∑ t ∈ Finset.range k, νt t (w t) +
        (φ (w - ∑ t ∈ Finset.range (k + 1), linftyTSSingle t (w t)) +
          linftyCoordDual φ k (linftyTrunc (μ k) (A k n) (w k))) ≤ φ y0 := by
      filter_upwards [h8.2 j k w hw (A k) (hA k)] with n hn
      have h := ih _ hn
      rw [linftyPeriodTrunc_drop, map_add, ← linftyCoordDual_apply] at h
      rwa [Finset.sum_congr rfl fun t ht => by
        rw [linftyPeriodTrunc_apply_of_ne (Finset.mem_range.1 ht).ne]] at h
    have hlim := (tendsto_const_nhds (x := ∑ t ∈ Finset.range k, νt t (w t))).add
      ((tendsto_const_nhds (x := φ (w - ∑ t ∈ Finset.range (k + 1),
        linftyTSSingle t (w t)))).add (hν k (w k)))
    have := le_of_tendsto hlim hev
    rw [Finset.sum_range_succ]
    linarith

/-- **Theorem 15.9** (p. 470). On the time–state space, under Assumptions 15.1, 15.2, 15.6, 15.7,
15.8′ and 15.9′, if `φ ∈ S*` supports the feasible allocation (conditions (4), (5)) and every
consumer has a strictly preferred point, then there is a continuous linear `ν` with
`‖ν‖ ≤ ‖φ‖` supporting the allocation and, as in (9),
`ν(x) = Σ_t ∫ p_t(z^t) x_t(z^t) dμ^t(z^t)` with every `p_t ∈ L¹(μ^t)`. -/
theorem theorem_15_9 [∀ t, IsFiniteMeasure (μ t)] {X : ι → Set (LinftyTimeState μ)}
    {u : ι → LinftyTimeState μ → ℝ} {Y : κ → Set (LinftyTimeState μ)}
    {x : ι → LinftyTimeState μ} {y : κ → LinftyTimeState μ}
    (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u) (h6 : Assumption15_6_timeState X Y)
    (h7 : Assumption15_7_timeState X u) (h8 : Assumption15_8' μ X Y) (h9 : Assumption15_9' μ X u)
    (hF : Feasible X Y x y) {φ : StrongDual ℝ (LinftyTimeState μ)}
    (hφ : SupportsAllocation X u Y x y φ) (hsat : ∀ i, ∃ xhat ∈ X i, u i (x i) < u i xhat) :
    ∃ ν : StrongDual ℝ (LinftyTimeState μ), ‖ν‖ ≤ ‖φ‖ ∧ SupportsAllocation X u Y x y ν ∧
      ∃ p : ∀ t, Ω t → ℝ, (∀ t, Integrable (p t) (μ t)) ∧
        ∀ z, HasSum (fun t => ∫ w, p t w * z t w ∂(μ t)) (ν z) := by
  obtain ⟨A, hA, νt, hνlim, hνp, ν, hνn, hνsum⟩ := exists_linftyTimeState_decomposition φ
  choose p hp hpν using hνp
  refine ⟨ν, hνn, supportsAllocation_of_limit_bounds (φ := φ) h1 h2 hF hsat ?_ ?_, p, hp,
    fun z => by simpa only [hpν] using hνsum z⟩
  · intro i z hz hlt
    have hev : ∀ᶠ T in atTop, φ (x i) ≤ ∑ t ∈ Finset.range (T + 1), νt t (z t) := by
      filter_upwards [h6.1 i z hz, h7 i z hz (x i) (hF.1 i) hlt] with T hT1 hT2
      have h := linftyTS_consumer_bound h8 h9 (hF.1 i) (hφ.1 i) hA hνlim (T + 1) _ hT1 hT2
      rw [linftyTimeTrunc_drop, map_zero, add_zero] at h
      rwa [Finset.sum_congr rfl (g := fun t => νt t (z t)) fun t ht => by
        simp only [linftyTimeTrunc_apply, Nat.lt_succ_iff.1 (Finset.mem_range.1 ht),
          ↓reduceIte]] at h
    exact ge_of_tendsto ((hνsum z).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)) hev
  · intro j w hw
    have hev : ∀ᶠ T in atTop, ∑ t ∈ Finset.range (T + 1), νt t (w t) ≤ φ (y j) := by
      filter_upwards [h6.2 j w hw] with T hT
      have h := linftyTS_firm_bound h8 (hφ.2 j) hA hνlim (T + 1) _ hT
      rw [linftyTimeTrunc_drop, map_zero, add_zero] at h
      rwa [Finset.sum_congr rfl (g := fun t => νt t (w t)) fun t ht => by
        simp only [linftyTimeTrunc_apply, Nat.lt_succ_iff.1 (Finset.mem_range.1 ht),
          ↓reduceIte]] at h
    exact le_of_tendsto ((hνsum w).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)) hev

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Sequence spaces, truncations, and Lemma 15.5

SLP §15.4, pp. 463–464. `E` is a real normed space, the one-period commodity space (the book's
`X`). The commodity space is `S = BddSeq E`, the space of sequences `x = (x₀, x₁, …)` in `E` with
`‖x‖ = sup_t ‖x_t‖ < ∞` (Mathlib's `lp (fun _ : ℕ => E) ∞`).

* `seqTrunc T` (p. 463): the truncation `x ↦ xᵀ = (x₀, …, x_T, 0, 0, …)`, a continuous linear map
  of norm at most one (`norm_seqTrunc_le`), and `seqTrunc_eq_sum_single`: `xᵀ` is the sum of the
  coordinate vectors `x_t` placed in position `t`, `t ≤ T`.
* `seqC00`: the subspace of sequences that are eventually zero.
* `coordFunctional φ t` (`ψ_t`, p. 464): `φ` composed with the embedding of `E` as the `t`-th
  coordinate.
* `sum_abs_coordFunctional_le` (proof of Lemma 15.5): `Σ_{t<n} |ψ_t(x_t)| ≤ ‖φ‖ ‖x‖`.
* `seqRegularPart φ` (`ψ`, (1)–(2), p. 463): the continuous linear functional
  `ψ(x) = Σ_t ψ_t(x_t)`.
* **Lemma 15.5** (`lemma_15_5`, p. 463): `ψ(x) = lim_T φ(xᵀ)` for every `x`; the series
  `Σ_t ψ_t(x_t)` converges absolutely to `ψ(x)`, with `Σ_t |ψ_t(x_t)| ≤ ‖φ‖ ‖x‖`; `‖ψ‖ ≤ ‖φ‖`;
  `φ − ψ` vanishes on `seqC00`; and `ψ` itself has no weight at infinity, `ψ(x) = lim_T ψ(xᵀ)`.
* Inner product forms (3) (p. 464): for `E = ℝ`, `ψ(x) = Σ_t p_t x_t` with `Σ_t |p_t| ≤ ‖φ‖`
  (`seqRegularPart_real`); for `E = ℝᴷ` with the max norm, `ψ(x) = Σ_t Σ_k p_{tk} x_{tk}` with
  `Σ_t Σ_k |p_{tk}| ≤ ‖φ‖` (`seqRegularPart_euclid`).

**Correction.** None: Lemma 15.5 is correct. The book's case `x = θ` in the proof is unnecessary,
and the summability of the price sequence `(p_t)` in (3) is implicit in the book; it is proved here.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology
open scoped ENNReal

/-- The commodity space `S` of §15.4 (p. 463): bounded sequences in `E` with the sup norm. -/
abbrev BddSeq (E : Type*) [NormedAddCommGroup E] : Type _ := ↥(lp (fun _ : ℕ => E) ∞)

variable {E : Type*} [NormedAddCommGroup E]

/-- Coordinates of an element of `BddSeq E` are bounded by its norm. -/
theorem norm_seq_coord_le (x : BddSeq E) (t : ℕ) : ‖x t‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x t

/-- An element of `BddSeq E` from a sequence bounded by `C ≥ 0`. -/
noncomputable def BddSeq.mk (f : ℕ → E) (C : ℝ) (hf : ∀ t, ‖f t‖ ≤ C) : BddSeq E :=
  ⟨f, memℓp_infty ⟨C, by rintro _ ⟨t, rfl⟩; exact hf t⟩⟩

/-- Coordinates of `BddSeq.mk`. -/
@[simp] theorem BddSeq.mk_apply (f : ℕ → E) (C : ℝ) (hf : ∀ t, ‖f t‖ ≤ C) (t : ℕ) :
    BddSeq.mk f C hf t = f t := rfl

/-- Coordinates of a finite sum of coordinate vectors. -/
theorem seq_sum_single_apply (s : Finset ℕ) (f : ℕ → E) (t : ℕ) :
    (∑ i ∈ s, lp.single ∞ i (f i) : BddSeq E) t = if t ∈ s then f t else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, lp.coeFn_add, Pi.add_apply, ih, lp.single_apply, Pi.single_apply]
    by_cases h : t = a
    · subst h; simp [ha]
    · simp [h]

variable [NormedSpace ℝ E]

/-- The truncation as a function: `xᵀ_t = x_t` for `t ≤ T` and `0` otherwise. -/
noncomputable def seqTruncFun (T : ℕ) (x : BddSeq E) : BddSeq E :=
  BddSeq.mk (fun t => if t ≤ T then x t else 0) ‖x‖ fun t => by
    split_ifs
    · exact norm_seq_coord_le x t
    · simp

omit [NormedSpace ℝ E] in
/-- The norm bound for truncations. -/
theorem norm_seqTruncFun_le (T : ℕ) (x : BddSeq E) : ‖seqTruncFun T x‖ ≤ ‖x‖ :=
  lp.norm_le_of_forall_le (norm_nonneg x) fun t => by
    change ‖(if t ≤ T then x t else 0)‖ ≤ ‖x‖
    split_ifs
    · exact norm_seq_coord_le x t
    · simp

/-- The **truncation** `x ↦ xᵀ = (x₀, …, x_T, 0, 0, …)` (p. 463), a continuous linear map. -/
noncomputable def seqTrunc (T : ℕ) : BddSeq E →L[ℝ] BddSeq E :=
  LinearMap.mkContinuous
    { toFun := seqTruncFun T
      map_add' := fun x y => by
        ext t
        change (if t ≤ T then (x + y) t else 0) =
          (if t ≤ T then x t else 0) + (if t ≤ T then y t else 0)
        split_ifs <;> simp
      map_smul' := fun c x => by
        ext t
        change (if t ≤ T then (c • x) t else 0) = c • (if t ≤ T then x t else 0)
        split_ifs <;> simp }
    1 fun x => by simpa using norm_seqTruncFun_le T x

/-- Coordinates of the truncation. -/
theorem seqTrunc_apply (T : ℕ) (x : BddSeq E) (t : ℕ) :
    seqTrunc T x t = if t ≤ T then x t else 0 := rfl

/-- Truncation does not increase the norm. -/
theorem norm_seqTrunc_le (T : ℕ) (x : BddSeq E) : ‖seqTrunc T x‖ ≤ ‖x‖ := norm_seqTruncFun_le T x

/-- The truncation is the sum of the coordinates placed in their positions:
`xᵀ = Σ_{t ≤ T} x̲_t`. -/
theorem seqTrunc_eq_sum_single (T : ℕ) (x : BddSeq E) :
    seqTrunc T x = ∑ t ∈ Finset.range (T + 1), lp.single ∞ t (x t) := by
  ext s
  rw [seqTrunc_apply, seq_sum_single_apply]
  simp

/-- Truncating twice truncates at the smaller index. -/
theorem seqTrunc_seqTrunc (T T' : ℕ) (x : BddSeq E) :
    seqTrunc T (seqTrunc T' x) = seqTrunc (min T T') x := by
  ext t
  simp only [seqTrunc_apply, le_min_iff]
  split_ifs <;> tauto

/-- The subspace `seqC00` of sequences that are eventually zero. -/
def seqC00 (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Submodule ℝ (BddSeq E) where
  carrier := {x | ∀ᶠ t in atTop, x t = 0}
  add_mem' := fun hx hy => (hx.and hy).mono fun t h => by simp [h.1, h.2]
  zero_mem' := Eventually.of_forall fun t => rfl
  smul_mem' := fun c x hx => hx.mono fun t h => by simp [h]

/-- Truncations are eventually zero. -/
theorem seqTrunc_mem_seqC00 (T : ℕ) (x : BddSeq E) : seqTrunc T x ∈ seqC00 E :=
  (eventually_gt_atTop T).mono fun t ht => by simp [seqTrunc_apply, not_le.2 ht]

/-- An eventually zero sequence equals its truncations far enough out. -/
theorem eventually_seqTrunc_eq_of_mem_seqC00 {x : BddSeq E} (hx : x ∈ seqC00 E) :
    ∀ᶠ T in atTop, seqTrunc T x = x := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hx
  filter_upwards [eventually_ge_atTop N] with T hT
  ext t
  rw [seqTrunc_apply]
  split_ifs with h
  · rfl
  · exact (hN t (hT.trans (not_le.1 h).le)).symm

/-- `ψ_t = φ ∘ (embedding of `E` as the `t`-th coordinate)` (p. 464). -/
noncomputable def coordFunctional (φ : StrongDual ℝ (BddSeq E)) (t : ℕ) : StrongDual ℝ E :=
  φ.comp (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => E) ∞ t)

/-- Value of `ψ_t`. -/
theorem coordFunctional_apply (φ : StrongDual ℝ (BddSeq E)) (t : ℕ) (a : E) :
    coordFunctional φ t a = φ (lp.single ∞ t a) := rfl

/-- `φ(xᵀ) = Σ_{t ≤ T} ψ_t(x_t)` (proof of Lemma 15.5). -/
theorem apply_seqTrunc_eq_sum (φ : StrongDual ℝ (BddSeq E)) (T : ℕ) (x : BddSeq E) :
    φ (seqTrunc T x) = ∑ t ∈ Finset.range (T + 1), coordFunctional φ t (x t) := by
  rw [seqTrunc_eq_sum_single, map_sum]
  rfl

/-- The key bound in the proof of Lemma 15.5: `Σ_{t<n} |ψ_t(x_t)| ≤ ‖φ‖ ‖x‖`. The book flips
the sign of each `x_t` so that every term is nonnegative and evaluates `φ` at the result. -/
theorem sum_abs_coordFunctional_le (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) (n : ℕ) :
    ∑ t ∈ Finset.range n, |coordFunctional φ t (x t)| ≤ ‖φ‖ * ‖x‖ := by
  set s : ℕ → ℝ := fun t => if 0 ≤ coordFunctional φ t (x t) then 1 else -1 with hs
  set y : BddSeq E := ∑ t ∈ Finset.range n, lp.single ∞ t (s t • x t) with hy
  have hsabs : ∀ t, ‖s t‖ = 1 := fun t => by simp only [hs]; split_ifs <;> simp
  have hyt : ∀ t, y t = if t ∈ Finset.range n then s t • x t else 0 := fun t => by
    rw [hy, seq_sum_single_apply]
  have hyn : ‖y‖ ≤ ‖x‖ := lp.norm_le_of_forall_le (norm_nonneg x) fun t => by
    rw [hyt]
    split_ifs
    · rw [norm_smul, hsabs, one_mul]; exact norm_seq_coord_le x t
    · simp
  have hφy : φ y = ∑ t ∈ Finset.range n, |coordFunctional φ t (x t)| := by
    rw [hy, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    change coordFunctional φ t (s t • x t) = _
    rw [map_smul, smul_eq_mul]
    simp only [hs]
    split_ifs with h
    · rw [one_mul, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.1 h)]; ring
  rw [← hφy]
  exact (le_abs_self _).trans ((φ.le_opNorm y).trans
    (mul_le_mul_of_nonneg_left hyn (norm_nonneg φ)))

/-- The series `Σ_t ψ_t(x_t)` converges absolutely. -/
theorem summable_abs_coordFunctional (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    Summable fun t => |coordFunctional φ t (x t)| :=
  summable_of_sum_range_le (fun _ => abs_nonneg _) (sum_abs_coordFunctional_le φ x)

/-- The series `Σ_t ψ_t(x_t)` converges. -/
theorem summable_coordFunctional (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    Summable fun t => coordFunctional φ t (x t) :=
  (summable_abs_coordFunctional φ x).of_abs

/-- `Σ_t |ψ_t(x_t)| ≤ ‖φ‖ ‖x‖`. -/
theorem tsum_abs_coordFunctional_le (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    ∑' t, |coordFunctional φ t (x t)| ≤ ‖φ‖ * ‖x‖ :=
  Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) (sum_abs_coordFunctional_le φ x)

/-- `ψ` as a linear map. -/
noncomputable def seqRegularPartLinear (φ : StrongDual ℝ (BddSeq E)) : BddSeq E →ₗ[ℝ] ℝ where
  toFun x := ∑' t, coordFunctional φ t (x t)
  map_add' x y := by
    have h : ∀ t, coordFunctional φ t ((x + y) t) =
        coordFunctional φ t (x t) + coordFunctional φ t (y t) := fun t => by
      rw [lp.coeFn_add, Pi.add_apply, map_add]
    simp only [h]
    exact (summable_coordFunctional φ x).tsum_add (summable_coordFunctional φ y)
  map_smul' c x := by
    have h : ∀ t, coordFunctional φ t ((c • x) t) = c * coordFunctional φ t (x t) := fun t => by
      rw [lp.coeFn_smul, Pi.smul_apply, map_smul, smul_eq_mul]
    simp only [h, RingHom.id_apply, smul_eq_mul]
    exact tsum_mul_left

/-- `|ψ(x)| ≤ ‖φ‖ ‖x‖`. -/
theorem abs_seqRegularPartLinear_le (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    ‖seqRegularPartLinear φ x‖ ≤ ‖φ‖ * ‖x‖ := by
  have h := norm_tsum_le_tsum_norm (f := fun t => coordFunctional φ t (x t))
    (by simpa only [Real.norm_eq_abs] using summable_abs_coordFunctional φ x)
  simp only [Real.norm_eq_abs] at h
  change |∑' t, coordFunctional φ t (x t)| ≤ ‖φ‖ * ‖x‖
  exact h.trans (tsum_abs_coordFunctional_le φ x)

/-- The **regular part** `ψ` of `φ` ((1)–(2), p. 463): `ψ(x) = Σ_t ψ_t(x_t) = lim_T φ(xᵀ)`. -/
noncomputable def seqRegularPart (φ : StrongDual ℝ (BddSeq E)) : StrongDual ℝ (BddSeq E) :=
  (seqRegularPartLinear φ).mkContinuous ‖φ‖ (abs_seqRegularPartLinear_le φ)

/-- `ψ(x) = Σ'_t ψ_t(x_t)`. -/
theorem seqRegularPart_apply (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    seqRegularPart φ x = ∑' t, coordFunctional φ t (x t) := rfl

/-- (2): `ψ(x) = Σ_t ψ_t(x_t)`, as a `HasSum`. -/
theorem hasSum_seqRegularPart (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    HasSum (fun t => coordFunctional φ t (x t)) (seqRegularPart φ x) :=
  (summable_coordFunctional φ x).hasSum

/-- (1): `ψ(x) = lim_T φ(xᵀ)`. -/
theorem tendsto_apply_seqTrunc (φ : StrongDual ℝ (BddSeq E)) (x : BddSeq E) :
    Tendsto (fun T => φ (seqTrunc T x)) atTop (𝓝 (seqRegularPart φ x)) := by
  simp only [apply_seqTrunc_eq_sum]
  exact (hasSum_seqRegularPart φ x).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- `‖ψ‖ ≤ ‖φ‖`. -/
theorem norm_seqRegularPart_le (φ : StrongDual ℝ (BddSeq E)) : ‖seqRegularPart φ‖ ≤ ‖φ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg φ) _

/-- `φ − ψ` vanishes on eventually zero sequences. -/
theorem seqRegularPart_eq_of_mem_seqC00 (φ : StrongDual ℝ (BddSeq E)) {x : BddSeq E}
    (hx : x ∈ seqC00 E) : seqRegularPart φ x = φ x := by
  refine tendsto_nhds_unique (tendsto_apply_seqTrunc φ x) ?_
  exact tendsto_const_nhds.congr' ((eventually_seqTrunc_eq_of_mem_seqC00 hx).mono fun T h => by
    simp only [h])

/-- `ψ(xᵀ) = φ(xᵀ)`. -/
theorem seqRegularPart_seqTrunc (φ : StrongDual ℝ (BddSeq E)) (T : ℕ) (x : BddSeq E) :
    seqRegularPart φ (seqTrunc T x) = φ (seqTrunc T x) :=
  seqRegularPart_eq_of_mem_seqC00 φ (seqTrunc_mem_seqC00 T x)

/-- `ψ` has no weight at infinity: `ψ(x) = lim_T ψ(xᵀ)`, i.e. `ψ` is its own regular part. -/
theorem seqRegularPart_seqRegularPart (φ : StrongDual ℝ (BddSeq E)) :
    seqRegularPart (seqRegularPart φ) = seqRegularPart φ := by
  ext x
  refine tendsto_nhds_unique (tendsto_apply_seqTrunc (seqRegularPart φ) x) ?_
  simp only [seqRegularPart_seqTrunc]
  exact tendsto_apply_seqTrunc φ x

/-- **Lemma 15.5** (p. 463). For every `φ ∈ S*`, `ψ(x) = lim_T φ(xᵀ)` exists for every `x` and
defines `ψ ∈ S*` with `‖ψ‖ ≤ ‖φ‖`; `ψ(x) = Σ_t ψ_t(x_t)` with `ψ_t ∈ E*`, the series converging
absolutely with `Σ_t |ψ_t(x_t)| ≤ ‖φ‖ ‖x‖`; `φ − ψ` vanishes on the eventually zero sequences;
and `ψ(x) = lim_T ψ(xᵀ)`. -/
theorem lemma_15_5 (φ : StrongDual ℝ (BddSeq E)) :
    (∀ x : BddSeq E, Tendsto (fun T => φ (seqTrunc T x)) atTop (𝓝 (seqRegularPart φ x))) ∧
    (∀ x : BddSeq E, HasSum (fun t => coordFunctional φ t (x t)) (seqRegularPart φ x)) ∧
    (∀ x : BddSeq E, ∑' t, |coordFunctional φ t (x t)| ≤ ‖φ‖ * ‖x‖) ∧
    ‖seqRegularPart φ‖ ≤ ‖φ‖ ∧
    (∀ x ∈ seqC00 E, (φ - seqRegularPart φ) x = 0) ∧
    (∀ x : BddSeq E,
      Tendsto (fun T => seqRegularPart φ (seqTrunc T x)) atTop (𝓝 (seqRegularPart φ x))) :=
  ⟨tendsto_apply_seqTrunc φ, hasSum_seqRegularPart φ, tsum_abs_coordFunctional_le φ,
    norm_seqRegularPart_le φ, fun x hx => by simp [seqRegularPart_eq_of_mem_seqC00 φ hx],
    fun x => by
      simpa [seqRegularPart_seqRegularPart] using tendsto_apply_seqTrunc (seqRegularPart φ) x⟩

/-! ### Inner product forms (3) -/

/-- The constant sequence `1` in `ℓ∞`. -/
noncomputable def oneSeq : BddSeq ℝ := BddSeq.mk (fun _ => 1) 1 fun _ => by simp

/-- `‖1‖ ≤ 1` in `ℓ∞`. -/
theorem norm_oneSeq_le : ‖oneSeq‖ ≤ 1 :=
  lp.norm_le_of_forall_le zero_le_one fun _ => by simp [oneSeq]

/-- (3) for `E = ℝ`: `ψ(x) = Σ_t p_t x_t` with `p_t = φ(e_t)` and `Σ_t |p_t| ≤ ‖φ‖`, so the price
sequence `p` is summable. -/
theorem seqRegularPart_real (φ : StrongDual ℝ (BddSeq ℝ)) :
    Summable (fun t => |φ (lp.single ∞ t 1)|) ∧ ∑' t, |φ (lp.single ∞ t 1)| ≤ ‖φ‖ ∧
    ∀ x : BddSeq ℝ, HasSum (fun t => φ (lp.single ∞ t 1) * x t) (seqRegularPart φ x) := by
  have hc : ∀ t (a : ℝ), coordFunctional φ t a = φ (lp.single ∞ t 1) * a := fun t a => by
    have : (lp.single ∞ t a : BddSeq ℝ) = a • (lp.single ∞ t 1 : BddSeq ℝ) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [coordFunctional_apply, this, map_smul, smul_eq_mul, mul_comm]
  have h1 : ∀ t, |coordFunctional φ t (oneSeq t)| = |φ (lp.single ∞ t 1)| := fun t => by
    simp [hc, oneSeq]
  refine ⟨?_, ?_, fun x => ?_⟩
  · simpa only [h1] using summable_abs_coordFunctional φ oneSeq
  · have := tsum_abs_coordFunctional_le φ oneSeq
    simp only [h1] at this
    exact this.trans (mul_le_of_le_one_right (norm_nonneg φ) norm_oneSeq_le)
  · simpa only [hc] using hasSum_seqRegularPart φ x

/-- (3) for `E = ℝᴷ` with the max norm: `ψ(x) = Σ_t Σ_k p_{tk} x_{tk}` with
`p_{tk} = φ(e_t ⊗ e_k)` and `Σ_t Σ_k |p_{tk}| ≤ ‖φ‖`. -/
theorem seqRegularPart_euclid {K : ℕ} (φ : StrongDual ℝ (BddSeq (Fin K → ℝ))) :
    Summable (fun t => ∑ k, |φ (lp.single ∞ t (Pi.single k 1))|) ∧
    ∑' t, ∑ k, |φ (lp.single ∞ t (Pi.single k 1))| ≤ ‖φ‖ ∧
    ∀ x : BddSeq (Fin K → ℝ),
      HasSum (fun t => ∑ k, φ (lp.single ∞ t (Pi.single k 1)) * x t k) (seqRegularPart φ x) := by
  set p : ℕ → Fin K → ℝ := fun t k => φ (lp.single ∞ t (Pi.single k 1)) with hp
  have hc : ∀ t (a : Fin K → ℝ), coordFunctional φ t a = ∑ k, p t k * a k := fun t a => by
    have ha : a = ∑ k, a k • (Pi.single k 1 : Fin K → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [ha]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  set sgn : ℕ → Fin K → ℝ := fun t k => if 0 ≤ p t k then 1 else -1 with hsgn
  have hsgn1 : ∀ t, ‖sgn t‖ ≤ 1 := fun t =>
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => by
      simp only [hsgn]; split_ifs <;> simp
  set z : BddSeq (Fin K → ℝ) := BddSeq.mk sgn 1 hsgn1 with hz
  have hzn : ‖z‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one fun t => hsgn1 t
  have habs : ∀ t, |coordFunctional φ t (z t)| = ∑ k, |p t k| := fun t => by
    have : coordFunctional φ t (z t) = ∑ k, |p t k| := by
      rw [hc]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hz, BddSeq.mk_apply, hsgn]
      split_ifs with h
      · rw [mul_one, abs_of_nonneg h]
      · rw [abs_of_neg (not_le.1 h)]; ring
    rw [this, abs_of_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _)]
  refine ⟨?_, ?_, fun x => ?_⟩
  · simpa only [habs] using summable_abs_coordFunctional φ z
  · have := tsum_abs_coordFunctional_le φ z
    simp only [habs] at this
    exact this.trans (mul_le_of_le_one_right (norm_nonneg φ) hzn)
  · simpa only [hc] using hasSum_seqRegularPart φ x

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Assumptions 15.6 and 15.7, and Exercise 15.10

SLP §15.4, p. 465. The commodity space is `S = BddSeq E` (bounded sequences in a real normed
space `E`), consumption sets `Xᵢ ⊆ S`, production sets `Yⱼ ⊆ S`.

* `SeqTruncClosed A`: `x ∈ A` implies `xᵀ ∈ A` for all `T` large enough.
  **Assumption 15.6** (`Assumption15_6`): every `Xᵢ` and every `Yⱼ` is `SeqTruncClosed`.
* `SeqTailInsensitive A v`: if `x, x′ ∈ A` and `v(x) > v(x′)` then `v(xᵀ) > v(x′)` for all `T` large
  enough (with `xᵀ ∈ A`). **Assumption 15.7** (`Assumption15_7`): every `(Xᵢ, uᵢ)` is
  `SeqTailInsensitive`.
* `SeqSemistrictQC A v`: one consumer's Assumption 15.2 (`assumption15_2_iff_seq`).
* `SeqTailInsensitive.of_tendsto`, `SeqTailInsensitive.of_liminf`: `v(xᵀ) → v(x)`, or just
  `liminf_T v(xᵀ) ≥ v(x)`, implies 15.7.
* **Exercise 15.10(a)** (`ex_15_10a`): for `C ⊆ E` convex with `0 ∈ C`, the set `seqSet C` of
  bounded sequences in `C` satisfies 15.1 and 15.6.
* **Exercise 15.10(b)** (`discountedUtility`, `u(x) = Σ_t βᵗ U(x_t)`): for `U` bounded on `C`,
  `u` satisfies 15.7 (`ex_15_10b_tail`), and 15.3 if `U` is continuous on `C`
  (`ex_15_10b_continuousOn`); with `U` concave, also 15.2 (`ex_15_10b`).
* **Exercise 15.10(c)** (`IsAggregator`, `IsAggregatorFixedPoint`, `seqShift`): a bounded
  continuous fixed point `u_W(x) = W(x₀, u_W(₁x))` of `T_W` satisfies 15.3 and 15.7 under
  (W1)–(W3) (`ex_15_10c_tail`), and 15.2 too when `W` is concave (`ex_15_10c`); since `W ≥ 0`,
  concavity already makes `W` increasing in its second argument
  (`seq_monotoneOn_of_concave_nonneg`), so (W4) is not needed.

**Corrections.**
* Exercise 15.10(b) is false for Assumption 15.2: `C = [0, 2]`, `U(c) = c²` (bounded,
  continuous, increasing, so 15.2 holds for `U` on `C`), `β = 1/2`, `x = (2, 0, 0, …)`,
  `x′ = (0, 2, 0, …)`: `u(x) = 4 > u(x′) = 2` but `u((x + x′)/2) = u(1, 1, 0, …) = 3/2`
  (`ex_15_10b_counterexample`). Concavity of `U` repairs it (`ex_15_10b`). Continuity of `U` is
  not needed for 15.7.
* Exercise 15.10(c) is false for Assumption 15.2 with an aggregator in the sense of §5.11
  ((W1)–(W3) only): `W(c, z) = min(c, 2)² + z/2` (`ex_15_10c_counterexample`). It is true if
  `W` is also concave, (W5) (`ex_15_10c`); the manual uses this silently via Exercise 5.11d.
  The transcription's NOTE asks for (W4) and (W5); (W5) alone suffices, because a nonnegative
  concave function on `[0, ∞)` is nondecreasing. Here `C ⊆ E` is any convex set containing `0`
  (the book: `C = ℝⁿ₊`), and the fixed point `u_W` is taken as given (any bounded, continuous,
  nonnegative fixed point, as in §5.11; its existence is Exercise 5.11d), not constructed.
* The manual's proof of 15.3 in (b) needs uniform continuity of `U`, which is not assumed; the
  proof here uses dominated convergence instead.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology
open scoped ENNReal

/-- One consumer's **Assumption 15.2** (semistrict quasi-concavity on `A`). -/
def SeqSemistrictQC {V : Type*} [AddCommGroup V] [Module ℝ V] (A : Set V) (v : V → ℝ) : Prop :=
  ∀ z ∈ A, ∀ z' ∈ A, v z' < v z → ∀ θ : ℝ, 0 < θ → θ < 1 → v z' < v (θ • z + (1 - θ) • z')

/-- Assumption 15.2 is `SeqSemistrictQC` for every consumer. -/
theorem assumption15_2_iff_seq {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] {ι : Type*}
    (X : ι → Set S) (u : ι → S → ℝ) : Assumption15_2 X u ↔ ∀ i, SeqSemistrictQC (X i) (u i) :=
  Iff.rfl

/-- The concavity inequality implies `SeqSemistrictQC`. -/
theorem SeqSemistrictQC.of_concave {V : Type*} [AddCommGroup V] [Module ℝ V] {A : Set V}
    {v : V → ℝ}
    (h : ∀ z ∈ A, ∀ z' ∈ A, ∀ θ : ℝ, 0 < θ → θ < 1 →
      θ * v z + (1 - θ) * v z' ≤ v (θ • z + (1 - θ) • z')) : SeqSemistrictQC A v :=
  fun z hz z' hz' hlt θ h0 h1 => by
    have := h z hz z' hz' θ h0 h1
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `A` is closed under truncations far enough out (one set's part of Assumption 15.6). -/
def SeqTruncClosed (A : Set (BddSeq E)) : Prop := ∀ x ∈ A, ∀ᶠ T in atTop, seqTrunc T x ∈ A

/-- One consumer's **Assumption 15.7**: if `v(x) > v(x′)` then `v(xᵀ) > v(x′)` for all `T` large
enough (and such that `xᵀ ∈ A`, since `v` only matters on `A`). -/
def SeqTailInsensitive (A : Set (BddSeq E)) (v : BddSeq E → ℝ) : Prop :=
  ∀ x ∈ A, ∀ x' ∈ A, v x' < v x → ∀ᶠ T in atTop, seqTrunc T x ∈ A → v x' < v (seqTrunc T x)

/-- **Assumption 15.6** (p. 465): truncations of consumption and production plans far enough out
are again consumption and production plans. -/
def Assumption15_6 {ι κ : Type*} (X : ι → Set (BddSeq E)) (Y : κ → Set (BddSeq E)) : Prop :=
  (∀ i, SeqTruncClosed (X i)) ∧ ∀ j, SeqTruncClosed (Y j)

/-- **Assumption 15.7** (p. 465): sufficiently distant consumption matters little. -/
def Assumption15_7 {ι : Type*} (X : ι → Set (BddSeq E)) (u : ι → BddSeq E → ℝ) : Prop :=
  ∀ i, SeqTailInsensitive (X i) (u i)

/-- Under `SeqTruncClosed`, `SeqTailInsensitive` gives `v(xᵀ) > v(x′)` for all large `T`. -/
theorem SeqTailInsensitive.eventually {A : Set (BddSeq E)} {v : BddSeq E → ℝ}
    (hv : SeqTailInsensitive A v) (hA : SeqTruncClosed A) {x x' : BddSeq E} (hx : x ∈ A)
    (hx' : x' ∈ A) (hlt : v x' < v x) :
    ∀ᶠ T in atTop, seqTrunc T x ∈ A ∧ v x' < v (seqTrunc T x) :=
  ((hA x hx).and (hv x hx x' hx' hlt)).mono fun _ h => ⟨h.1, h.2 h.1⟩

/-- `liminf_T v(xᵀ) ≥ v(x)` (in the form `∀ c < v(x), eventually c < v(xᵀ)`) implies 15.7. -/
theorem SeqTailInsensitive.of_liminf {A : Set (BddSeq E)} {v : BddSeq E → ℝ}
    (h : ∀ x ∈ A, ∀ c < v x, ∀ᶠ T in atTop, c < v (seqTrunc T x)) : SeqTailInsensitive A v :=
  fun x hx _ _ hlt => (h x hx _ hlt).mono fun _ h' _ => h'

/-- `v(xᵀ) → v(x)` for every `x ∈ A` implies 15.7 (the "if" of Exercise 15.11(b)). -/
theorem SeqTailInsensitive.of_tendsto {A : Set (BddSeq E)} {v : BddSeq E → ℝ}
    (h : ∀ x ∈ A, Tendsto (fun T => v (seqTrunc T x)) atTop (𝓝 (v x))) : SeqTailInsensitive A v :=
  SeqTailInsensitive.of_liminf fun x hx _ hc => (h x hx).eventually (lt_mem_nhds hc)

/-! ### Exercise 15.10(a) -/

/-- The set `C × C × ⋯` of bounded sequences with every term in `C`. -/
def seqSet (C : Set E) : Set (BddSeq E) := {x | ∀ t, x t ∈ C}

/-- Coordinates of a linear combination. -/
theorem seq_coord_combo (a b : ℝ) (x y : BddSeq E) (t : ℕ) :
    (a • x + b • y) t = a • x t + b • y t := by
  rw [lp.coeFn_add, lp.coeFn_smul, lp.coeFn_smul]; rfl

/-- `seqSet C` is convex when `C` is. -/
theorem convex_seqSet {C : Set E} (hC : Convex ℝ C) : Convex ℝ (seqSet C) :=
  fun x hx y hy a b ha hb hab t => by
    rw [seq_coord_combo]; exact hC (hx t) (hy t) ha hb hab

/-- Truncations of sequences in `C` stay in `C` when `0 ∈ C`. -/
theorem seqTrunc_mem_seqSet {C : Set E} (h0 : (0 : E) ∈ C) {x : BddSeq E} (hx : x ∈ seqSet C)
    (T : ℕ) : seqTrunc T x ∈ seqSet C := fun t => by
  rw [seqTrunc_apply]; split_ifs
  · exact hx t
  · exact h0

/-- **Exercise 15.10(a)**: `Xᵢ = C × C × ⋯` satisfies Assumptions 15.1 and 15.6. -/
theorem ex_15_10a {C : Set E} (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) :
    Convex ℝ (seqSet C) ∧ SeqTruncClosed (seqSet C) :=
  ⟨convex_seqSet hC, fun _ hx => Eventually.of_forall (seqTrunc_mem_seqSet h0 hx)⟩

/-! ### Exercise 15.10(b) -/

/-- The **discounted utility** `u(x) = Σ_t βᵗ U(x_t)`. -/
noncomputable def discountedUtility (β : ℝ) (U : E → ℝ) (x : BddSeq E) : ℝ :=
  ∑' t, β ^ t * U (x t)

omit [NormedSpace ℝ E] in
/-- The terms `βᵗ U(x_t)` are bounded by `M βᵗ` on `C × C × ⋯`. -/
theorem norm_discounted_term_le {β : ℝ} (hβ0 : 0 ≤ β) {C : Set E} {U : E → ℝ} {M : ℝ}
    (hU : ∀ c ∈ C, |U c| ≤ M) {x : BddSeq E} (hx : x ∈ seqSet C) (t : ℕ) :
    ‖β ^ t * U (x t)‖ ≤ M * β ^ t := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
  exact mul_le_mul_of_nonneg_right (hU _ (hx t)) (pow_nonneg hβ0 t)

omit [NormedSpace ℝ E] in
/-- The discounted utility series converges on `C × C × ⋯`. -/
theorem summable_discounted {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set E} {U : E → ℝ}
    {M : ℝ} (hU : ∀ c ∈ C, |U c| ≤ M) {x : BddSeq E} (hx : x ∈ seqSet C) :
    Summable fun t => β ^ t * U (x t) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M)
    (norm_discounted_term_le hβ0 hU hx)

/-- For `U` bounded on `C ∋ 0`: `u(xᵀ) → u(x)` (dominated convergence). -/
theorem tendsto_discountedUtility_seqTrunc {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set E}
    (h0 : (0 : E) ∈ C) {U : E → ℝ} {M : ℝ} (hU : ∀ c ∈ C, |U c| ≤ M) {x : BddSeq E}
    (hx : x ∈ seqSet C) :
    Tendsto (fun T => discountedUtility β U (seqTrunc T x)) atTop
      (𝓝 (discountedUtility β U x)) := by
  refine tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M) (fun t => ?_)
    (Eventually.of_forall fun T t => norm_discounted_term_le hβ0 hU (seqTrunc_mem_seqSet h0 hx T) t)
  refine tendsto_const_nhds.congr' ((eventually_ge_atTop t).mono fun T hT => ?_)
  simp [seqTrunc_apply, hT]

/-- **Exercise 15.10(b)**, Assumption 15.7: for `U` bounded on `C ∋ 0` and `0 ≤ β < 1`, the
discounted utility satisfies 15.7. (Continuity of `U` is not needed.) -/
theorem ex_15_10b_tail {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set E} (h0 : (0 : E) ∈ C)
    {U : E → ℝ} {M : ℝ} (hU : ∀ c ∈ C, |U c| ≤ M) :
    SeqTailInsensitive (seqSet C) (discountedUtility β U) :=
  SeqTailInsensitive.of_tendsto fun _ hx => tendsto_discountedUtility_seqTrunc hβ0 hβ1 h0 hU hx

omit [NormedSpace ℝ E] in
/-- Evaluation at a coordinate is continuous on `BddSeq E`. -/
theorem continuous_seq_coord (t : ℕ) : Continuous fun y : BddSeq E => y t :=
  LipschitzWith.continuous (K := 1) <| LipschitzWith.of_dist_le_mul fun y z => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← Pi.sub_apply, ← lp.coeFn_sub]
    exact norm_seq_coord_le _ t

omit [NormedSpace ℝ E] in
/-- **Exercise 15.10(b)**, Assumption 15.3: for `U` bounded and continuous on `C`, the
discounted utility is continuous on `C × C × ⋯` in the sup norm (dominated convergence; the
manual's argument needs uniform continuity of `U`). -/
theorem ex_15_10b_continuousOn {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set E} {U : E → ℝ}
    {M : ℝ} (hU : ∀ c ∈ C, |U c| ≤ M) (hUc : ContinuousOn U C) :
    ContinuousOn (discountedUtility β U) (seqSet C) := by
  intro x hx
  refine tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M) (fun t => ?_)
    (eventually_nhdsWithin_of_forall fun y hy t => norm_discounted_term_le hβ0 hU hy t)
  refine tendsto_const_nhds.mul ((hUc (x t) (hx t)).tendsto.comp ?_)
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => hy t⟩
  exact ((continuous_seq_coord t).tendsto x).mono_left nhdsWithin_le_nhds

/-- The concavity inequality for the discounted utility of a concave `U`. -/
theorem discountedUtility_concave {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set E}
    {U : E → ℝ} {M : ℝ} (hU : ∀ c ∈ C, |U c| ≤ M) (hUcv : ConcaveOn ℝ C U) {x x' : BddSeq E}
    (hx : x ∈ seqSet C) (hx' : x' ∈ seqSet C) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * discountedUtility β U x + (1 - θ) * discountedUtility β U x' ≤
      discountedUtility β U (θ • x + (1 - θ) • x') := by
  have hmem : θ • x + (1 - θ) • x' ∈ seqSet C :=
    convex_seqSet hUcv.1 hx hx' h0 (by linarith) (by ring)
  have hs := summable_discounted hβ0 hβ1 hU hx
  have hs' := summable_discounted hβ0 hβ1 hU hx'
  unfold discountedUtility
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hs.mul_left θ).tsum_add (hs'.mul_left (1 - θ))]
  refine ((hs.mul_left θ).add (hs'.mul_left (1 - θ))).tsum_le_tsum (fun t => ?_)
    (summable_discounted hβ0 hβ1 hU hmem)
  have hc := hUcv.2 (hx t) (hx' t) h0 (by linarith : 0 ≤ 1 - θ) (by ring)
  rw [seq_coord_combo]
  simp only [smul_eq_mul] at hc
  have hb : 0 ≤ β ^ t := pow_nonneg hβ0 t
  nlinarith [mul_le_mul_of_nonneg_left hc hb]

/-- **Exercise 15.10(b)**, corrected: for `U` bounded, continuous and **concave** on a set
`C ∋ 0`, and `0 ≤ β < 1`, the discounted utility satisfies Assumptions 15.2, 15.3 and 15.7. -/
theorem ex_15_10b {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {C : Set E} (h0 : (0 : E) ∈ C)
    {U : E → ℝ} {M : ℝ} (hU : ∀ c ∈ C, |U c| ≤ M) (hUc : ContinuousOn U C)
    (hUcv : ConcaveOn ℝ C U) :
    SeqSemistrictQC (seqSet C) (discountedUtility β U) ∧
      ContinuousOn (discountedUtility β U) (seqSet C) ∧
      SeqTailInsensitive (seqSet C) (discountedUtility β U) :=
  ⟨SeqSemistrictQC.of_concave fun _ hx _ hx' _ h0' h1' =>
      discountedUtility_concave hβ0 hβ1 hU hUcv hx hx' h0'.le h1'.le,
    ex_15_10b_continuousOn hβ0 hβ1 hU hUc, ex_15_10b_tail hβ0 hβ1 h0 hU⟩

/-- The utilities of `x = (2, 0, 0, …)`, `x′ = (0, 2, 0, …)` and `(x + x′)/2 = (1, 1, 0, …)` for
`β = 1/2` and any `U` with `U(0) = 0`. -/
theorem discountedUtility_half_values (U : ℝ → ℝ) (hU0 : U 0 = 0) :
    discountedUtility (1 / 2) U (lp.single ∞ 0 2) = U 2 ∧
    discountedUtility (1 / 2) U (lp.single ∞ 1 2) = U 2 / 2 ∧
    discountedUtility (1 / 2) U ((1 / 2 : ℝ) • lp.single ∞ 0 2 +
      (1 - 1 / 2 : ℝ) • lp.single ∞ 1 2) = U 1 + U 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold discountedUtility
    rw [tsum_eq_single 0]
    · simp
    · intro t ht; simp [ht, hU0]
  · unfold discountedUtility
    rw [tsum_eq_single 1]
    · simp; ring
    · intro t ht; simp [ht, hU0]
  · unfold discountedUtility
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [seq_coord_combo, Finset.sum_range_succ, Pi.single_apply]; ring_nf
    · intro t ht
      have h0 : t ≠ 0 := fun h => ht (by simp [h])
      have h1 : t ≠ 1 := fun h => ht (by simp [h])
      simp [seq_coord_combo, h0, h1, hU0]

/-- **Exercise 15.10(b) is false for Assumption 15.2.** With `C = [0, 2]`, `U(c) = c²` (bounded
and continuous on `C`, and satisfying 15.2 on `C`) and `β = 1/2`, the discounted utility does not
satisfy 15.2. -/
theorem ex_15_10b_counterexample :
    (∀ c ∈ Set.Icc (0 : ℝ) 2, |c ^ 2| ≤ 4) ∧ ContinuousOn (fun c : ℝ => c ^ 2) (Set.Icc 0 2) ∧
    SeqSemistrictQC (Set.Icc (0 : ℝ) 2) (fun c => c ^ 2) ∧
    ¬ SeqSemistrictQC (seqSet (Set.Icc (0 : ℝ) 2)) (discountedUtility (1 / 2) fun c => c ^ 2) := by
  refine ⟨fun c hc => ?_, (continuous_pow 2).continuousOn, fun c hc c' hc' hlt θ h0 h1 => ?_,
    fun h => ?_⟩
  · rw [abs_of_nonneg (sq_nonneg c)]; nlinarith [hc.1, hc.2]
  · have hcc : c' < c := lt_of_pow_lt_pow_left₀ 2 hc.1 hlt
    have : c' < θ • c + (1 - θ) • c' := by simp only [smul_eq_mul]; nlinarith
    exact pow_lt_pow_left₀ this hc'.1 two_ne_zero
  · obtain ⟨h1, h2, h3⟩ := discountedUtility_half_values (fun c : ℝ => c ^ 2) (by norm_num)
    have hx : (lp.single ∞ 0 (2 : ℝ) : BddSeq ℝ) ∈ seqSet (Set.Icc (0 : ℝ) 2) := fun t => by
      rw [lp.single_apply, Pi.single_apply]; split_ifs <;> norm_num
    have hx' : (lp.single ∞ 1 (2 : ℝ) : BddSeq ℝ) ∈ seqSet (Set.Icc (0 : ℝ) 2) := fun t => by
      rw [lp.single_apply, Pi.single_apply]; split_ifs <;> norm_num
    have := h _ hx _ hx' (by rw [h1, h2]; norm_num) (1 / 2) (by norm_num) (by norm_num)
    rw [h2, h3] at this
    norm_num at this

/-! ### Exercise 15.10(c) -/

/-- The **seqShift** `₁x = (x₁, x₂, …)`. -/
noncomputable def seqShift : BddSeq E →L[ℝ] BddSeq E :=
  LinearMap.mkContinuous
    { toFun := fun x => BddSeq.mk (fun t => x (t + 1)) ‖x‖ fun t => norm_seq_coord_le x _
      map_add' := fun x y => by ext t; simp
      map_smul' := fun c x => by ext t; simp }
    1 fun x => by
      rw [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg x) fun t => norm_seq_coord_le x _

/-- Coordinates of the seqShift. -/
theorem seqShift_apply (x : BddSeq E) (t : ℕ) : seqShift x t = x (t + 1) := rfl

/-- Shifting a truncation: `₁(x^{T+1}) = (₁x)ᵀ`. -/
theorem seqShift_seqTrunc_succ (T : ℕ) (x : BddSeq E) :
    seqShift (seqTrunc (T + 1) x) = seqTrunc T (seqShift x) := by
  ext t
  simp only [seqShift_apply, seqTrunc_apply]
  split_ifs <;> first | rfl | omega

/-- The seqShift maps `C × C × ⋯` into itself. -/
theorem seqShift_mem_seqSet {C : Set E} {x : BddSeq E} (hx : x ∈ seqSet C) :
    seqShift x ∈ seqSet C :=
  fun t => hx (t + 1)

/-- An **aggregator function** on `C × ℝ₊` in the sense of §5.11 (pp. 114–116): continuous,
nonnegative, (W1) `W(0, 0) = 0`, (W2) `W(·, z)` bounded on `C`, (W3) `W` is a contraction of
modulus `β ∈ (0, 1)` in `z`. -/
structure IsAggregator (C : Set E) (W : E → ℝ → ℝ) (β : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  continuousOn : ContinuousOn (fun p : E × ℝ => W p.1 p.2) (C ×ˢ Set.Ici 0)
  zero : W 0 0 = 0
  bounded : ∀ z : ℝ, 0 ≤ z → ∃ B, ∀ c ∈ C, |W c z| ≤ B
  nonneg : ∀ c ∈ C, ∀ z : ℝ, 0 ≤ z → 0 ≤ W c z
  lipschitz : ∀ c ∈ C, ∀ z : ℝ, 0 ≤ z → ∀ z' : ℝ, 0 ≤ z' → |W c z - W c z'| ≤ β * |z - z'|

/-- `v` is a **fixed point of `T_W`** in the space of §5.11: bounded, continuous (sup norm) and
nonnegative on `C × C × ⋯`, with `v(x) = W(x₀, v(₁x))`. -/
structure IsAggregatorFixedPoint (C : Set E) (W : E → ℝ → ℝ) (v : BddSeq E → ℝ) : Prop where
  bounded : ∃ B, ∀ x ∈ seqSet C, |v x| ≤ B
  continuousOn : ContinuousOn v (seqSet C)
  nonneg : ∀ x ∈ seqSet C, 0 ≤ v x
  fixed : ∀ x ∈ seqSet C, v x = W (x 0) (v (seqShift x))

/-- The truncation bound of Exercise 5.11d: `|v(x) − v(xᵀ)| ≤ 2Bβᵀ`. -/
theorem aggregator_seqTrunc_bound {C : Set E} (h0 : (0 : E) ∈ C) {W : E → ℝ → ℝ} {β : ℝ}
    (hW : IsAggregator C W β) {v : BddSeq E → ℝ} (hv : IsAggregatorFixedPoint C W v) {B : ℝ}
    (hB : ∀ x ∈ seqSet C, |v x| ≤ B) (T : ℕ) :
    ∀ x ∈ seqSet C, |v x - v (seqTrunc T x)| ≤ 2 * B * β ^ T := by
  induction T with
  | zero =>
    intro x hx
    have h1 := hB x hx
    have h2 := hB _ (seqTrunc_mem_seqSet h0 hx 0)
    rw [pow_zero, mul_one]
    calc |v x - v (seqTrunc 0 x)| ≤ |v x| + |v (seqTrunc 0 x)| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  | succ T ih =>
    intro x hx
    have htx := seqTrunc_mem_seqSet h0 hx (T + 1)
    have hsx := seqShift_mem_seqSet hx
    rw [hv.fixed x hx, hv.fixed _ htx, seqShift_seqTrunc_succ]
    have h00 : seqTrunc (T + 1) x 0 = x 0 := by simp [seqTrunc_apply]
    rw [h00]
    calc |W (x 0) (v (seqShift x)) - W (x 0) (v (seqTrunc T (seqShift x)))|
        ≤ β * |v (seqShift x) - v (seqTrunc T (seqShift x))| :=
          hW.lipschitz _ (hx 0) _ (hv.nonneg _ hsx) _
            (hv.nonneg _ (seqTrunc_mem_seqSet h0 hsx T))
      _ ≤ β * (2 * B * β ^ T) := mul_le_mul_of_nonneg_left (ih _ hsx) hW.beta_pos.le
      _ = 2 * B * β ^ (T + 1) := by ring

/-- **Exercise 15.10(c)**, Assumptions 15.3 and 15.7, under (W1)–(W3) only. -/
theorem ex_15_10c_tail {C : Set E} (h0 : (0 : E) ∈ C) {W : E → ℝ → ℝ} {β : ℝ}
    (hW : IsAggregator C W β) {v : BddSeq E → ℝ} (hv : IsAggregatorFixedPoint C W v) :
    ContinuousOn v (seqSet C) ∧ SeqTailInsensitive (seqSet C) v := by
  refine ⟨hv.continuousOn, SeqTailInsensitive.of_tendsto fun x hx => ?_⟩
  obtain ⟨B, hB⟩ := hv.bounded
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun T => ?_)
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hW.beta_pos.le
      hW.beta_lt_one).const_mul (2 * B))
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact aggregator_seqTrunc_bound h0 hW hv hB T x hx

/-- A nonnegative concave function on `[0, ∞)` is nondecreasing. -/
theorem seq_monotoneOn_of_concave_nonneg {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f)
    (h0 : ∀ z, 0 ≤ z → 0 ≤ f z) : MonotoneOn f (Set.Ici 0) := by
  intro a ha b hb hab
  rcases hab.lt_or_eq with hlt | rfl
  · by_contra hgt
    have hgt' : f b < f a := not_le.1 hgt
    have hfb := h0 b (Set.mem_Ici.1 hb)
    -- go far beyond `b`, where the chord through `a`, `b` forces `f < 0`
    set z := b + (f b + 1) * (b - a) / (f a - f b) with hz
    have hpos : 0 < (f b + 1) * (b - a) / (f a - f b) :=
      div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    have hbz : b < z := by rw [hz]; linarith
    have hz0 : 0 ≤ z := by linarith [Set.mem_Ici.1 hb]
    have hadj := hf.slope_anti_adjacent ha (Set.mem_Ici.2 hz0) hlt hbz
    rw [div_le_div_iff₀ (by linarith) (by linarith)] at hadj
    have hzb : z - b = (f b + 1) * (b - a) / (f a - f b) := by rw [hz]; ring
    rw [hzb] at hadj
    have hne : f a - f b ≠ 0 := (sub_pos.2 hgt').ne'
    have key : (f b - f a) * ((f b + 1) * (b - a) / (f a - f b)) = -((f b + 1) * (b - a)) := by
      field_simp
      ring
    have hfz := h0 z hz0
    nlinarith
  · exact le_rfl

/-- `W(c, ·)` is nondecreasing on `ℝ₊` when `W` is a concave aggregator. -/
theorem aggregator_monotone {C : Set E} {W : E → ℝ → ℝ} {β : ℝ} (hW : IsAggregator C W β)
    (hW5 : ConcaveOn ℝ (C ×ˢ Set.Ici 0) fun p : E × ℝ => W p.1 p.2) {c : E} (hc : c ∈ C) :
    MonotoneOn (W c) (Set.Ici 0) := by
  refine seq_monotoneOn_of_concave_nonneg ⟨convex_Ici 0, fun z hz z' hz' a b ha hb hab => ?_⟩
    (hW.nonneg c hc)
  have h := hW5.2 (x := (c, z)) (y := (c, z')) ⟨hc, hz⟩ ⟨hc, hz'⟩ ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk] at h
  rwa [Convex.combo_self hab] at h

/-- The concavity inequality for `v`, up to `4Bβᵏ`, by induction on `k`. -/
theorem aggregator_concave_approx {C : Set E} (hC : Convex ℝ C) {W : E → ℝ → ℝ} {β : ℝ}
    (hW : IsAggregator C W β)
    (hW5 : ConcaveOn ℝ (C ×ˢ Set.Ici 0) fun p : E × ℝ => W p.1 p.2) {v : BddSeq E → ℝ}
    (hv : IsAggregatorFixedPoint C W v) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ seqSet C, |v x| ≤ B) (k : ℕ) :
    ∀ x ∈ seqSet C, ∀ x' ∈ seqSet C, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      θ * v x + (1 - θ) * v x' - 4 * B * β ^ k ≤ v (θ • x + (1 - θ) • x') := by
  induction k with
  | zero =>
    intro x hx x' hx' θ h0 h1
    have hm := convex_seqSet hC hx hx' h0 (by linarith : 0 ≤ 1 - θ) (by ring)
    have e1 := abs_le.1 (hB x hx)
    have e2 := abs_le.1 (hB x' hx')
    have e3 := abs_le.1 (hB _ hm)
    nlinarith
  | succ k ih =>
    intro x hx x' hx' θ h0 h1
    have h1θ : 0 ≤ 1 - θ := by linarith
    have hm := convex_seqSet hC hx hx' h0 h1θ (by ring)
    have hsx := seqShift_mem_seqSet hx
    have hsx' := seqShift_mem_seqSet hx'
    set c := θ • x 0 + (1 - θ) • x' 0 with hc
    set z := θ * v (seqShift x) + (1 - θ) * v (seqShift x') with hz
    set w := v (seqShift (θ • x + (1 - θ) • x')) with hw
    have hshift : seqShift (θ • x + (1 - θ) • x') = θ • seqShift x + (1 - θ) • seqShift x' := by
      rw [map_add, map_smul, map_smul]
    have hwz : z - 4 * B * β ^ k ≤ w := by
      rw [hw, hshift]; exact ih _ hsx _ hsx' θ h0 h1
    have hcC : c ∈ C := hC (hx 0) (hx' 0) h0 h1θ (by ring)
    have hz0 : 0 ≤ z := by
      have := hv.nonneg _ hsx; have := hv.nonneg _ hsx'; positivity
    have hw0 : 0 ≤ w := hv.nonneg _ (seqShift_mem_seqSet hm)
    have hWw : W c z - β * (4 * B * β ^ k) ≤ W c w := by
      rcases le_total z w with hle | hle
      · have := aggregator_monotone hW hW5 hcC hz0 hw0 hle
        have : 0 ≤ β * (4 * B * β ^ k) := by
          have := hW.beta_pos.le; positivity
        linarith
      · have hl := hW.lipschitz c hcC z hz0 w hw0
        rw [abs_of_nonneg (sub_nonneg.2 hle)] at hl
        have h2 := (abs_le.1 hl).2
        have h3 := mul_le_mul_of_nonneg_left (show z - w ≤ 4 * B * β ^ k by linarith)
          hW.beta_pos.le
        linarith
    have hcv := hW5.2 (x := (x 0, v (seqShift x))) (y := (x' 0, v (seqShift x')))
      ⟨hx 0, hv.nonneg _ hsx⟩ ⟨hx' 0, hv.nonneg _ hsx'⟩ h0 h1θ (by ring)
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hcv
    have hvm : v (θ • x + (1 - θ) • x') = W c w := by
      rw [hv.fixed _ hm, seq_coord_combo]
    rw [hvm, hv.fixed x hx, hv.fixed x' hx']
    have : W c z = W (θ • x 0 + (1 - θ) • x' 0) (θ * v (seqShift x) + (1 - θ) * v (seqShift x')) :=
      rfl
    rw [pow_succ]
    nlinarith

/-- **Exercise 15.10(c)**, corrected: if the aggregator `W` is also concave on `C × ℝ₊`
(property (W5) of §5.11, used silently by the manual via Exercise 5.11d; (W4) is not needed), the
fixed point `u_W` satisfies Assumptions 15.2, 15.3 and 15.7. -/
theorem ex_15_10c {C : Set E} (hC : Convex ℝ C) (h0 : (0 : E) ∈ C) {W : E → ℝ → ℝ} {β : ℝ}
    (hW : IsAggregator C W β)
    (hW5 : ConcaveOn ℝ (C ×ˢ Set.Ici 0) fun p : E × ℝ => W p.1 p.2) {v : BddSeq E → ℝ}
    (hv : IsAggregatorFixedPoint C W v) :
    SeqSemistrictQC (seqSet C) v ∧ ContinuousOn v (seqSet C) ∧ SeqTailInsensitive (seqSet C) v := by
  refine ⟨SeqSemistrictQC.of_concave fun x hx x' hx' θ h0' h1' => ?_, ex_15_10c_tail h0 hW hv⟩
  obtain ⟨B, hB⟩ := hv.bounded
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x hx)
  have hlim : Tendsto (fun k : ℕ => θ * v x + (1 - θ) * v x' - 4 * B * β ^ k) atTop
      (𝓝 (θ * v x + (1 - θ) * v x')) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hW.beta_pos.le
      hW.beta_lt_one).const_mul (4 * B)).const_sub (θ * v x + (1 - θ) * v x')
  exact le_of_tendsto' hlim
    fun k => aggregator_concave_approx hC hW hW5 hv hB0 hB k x hx x' hx' θ h0'.le h1'.le

/-- **Exercise 15.10(c) is false for Assumption 15.2** with an aggregator in the sense of §5.11
((W1)–(W3) only): on `C = ℝ₊`, `W(c, z) = min(c, 2)² + z/2` is an aggregator with modulus `1/2`,
`u_W(x) = Σ_t (1/2)ᵗ min(x_t, 2)²` is its bounded continuous fixed point, and `u_W` violates 15.2
at `x = (2, 0, …)`, `x′ = (0, 2, 0, …)`, `θ = 1/2`. -/
theorem ex_15_10c_counterexample :
    IsAggregator (Set.Ici (0 : ℝ)) (fun c z => min c 2 ^ 2 + z / 2) (1 / 2) ∧
    IsAggregatorFixedPoint (Set.Ici (0 : ℝ)) (fun c z => min c 2 ^ 2 + z / 2)
      (discountedUtility (1 / 2) fun c => min c 2 ^ 2) ∧
    ¬ SeqSemistrictQC (seqSet (Set.Ici (0 : ℝ)))
      (discountedUtility (1 / 2) fun c => min c 2 ^ 2) := by
  have hU : ∀ c ∈ Set.Ici (0 : ℝ), |min c 2 ^ 2| ≤ 4 := fun c hc => by
    have h1 : 0 ≤ min c 2 := le_min hc (by norm_num)
    have h2 : min c 2 ≤ 2 := min_le_right _ _
    rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  have hβ0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hβ1 : (1 / 2 : ℝ) < 1 := by norm_num
  refine ⟨⟨by norm_num, by norm_num, ?_, by norm_num, fun z _ => ⟨4 + |z / 2|, fun c hc => ?_⟩,
    fun c hc z hz => by positivity, fun c _ z _ z' _ => ?_⟩, ⟨⟨8, fun x hx => ?_⟩, ?_,
    fun x hx => ?_, fun x hx => ?_⟩, fun h => ?_⟩
  · exact (((continuous_fst.min continuous_const).pow 2).add
      (continuous_snd.div_const 2)).continuousOn
  · exact (abs_add_le _ _).trans (by linarith [hU c hc])
  · rw [show min c 2 ^ 2 + z / 2 - (min c 2 ^ 2 + z' / 2) = (1 / 2) * (z - z') by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  · have hs := summable_discounted hβ0 hβ1 hU hx
    have h := norm_tsum_le_tsum_norm hs.norm
    refine h.trans ?_
    calc ∑' t, ‖(1 / 2 : ℝ) ^ t * min (x t) 2 ^ 2‖ ≤ ∑' t, 4 * (1 / 2 : ℝ) ^ t :=
          hs.norm.tsum_le_tsum (norm_discounted_term_le hβ0 hU hx)
            ((summable_geometric_of_lt_one hβ0 hβ1).mul_left 4)
      _ = 8 := by rw [tsum_mul_left, tsum_geometric_two]; norm_num
  · exact ex_15_10b_continuousOn hβ0 hβ1 hU
      ((continuous_id.min continuous_const).pow 2).continuousOn
  · exact tsum_nonneg fun t => by positivity
  · have hs := summable_discounted hβ0 hβ1 hU hx
    unfold discountedUtility
    have e : ∑' b, (1 / 2 : ℝ) ^ (b + 1) * min (x (b + 1)) 2 ^ 2 =
        (∑' t, (1 / 2 : ℝ) ^ t * min (seqShift x t) 2 ^ 2) / 2 := by
      rw [← tsum_div_const]
      exact tsum_congr fun b => by rw [seqShift_apply]; ring
    rw [hs.tsum_eq_zero_add, e, pow_zero, one_mul]
  · obtain ⟨h1, h2, h3⟩ := discountedUtility_half_values (fun c : ℝ => min c 2 ^ 2)
      (by norm_num)
    have hx : (lp.single ∞ 0 (2 : ℝ) : BddSeq ℝ) ∈ seqSet (Set.Ici (0 : ℝ)) := fun t => by
      rw [lp.single_apply, Pi.single_apply]; split_ifs <;> norm_num
    have hx' : (lp.single ∞ 1 (2 : ℝ) : BddSeq ℝ) ∈ seqSet (Set.Ici (0 : ℝ)) := fun t => by
      rw [lp.single_apply, Pi.single_apply]; split_ifs <;> norm_num
    have := h _ hx _ hx' (by rw [h1, h2]; norm_num) (1 / 2) (by norm_num) (by norm_num)
    rw [h2, h3] at this
    norm_num at this

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Discounted sums, the tail distance, and functionals with all their weight at infinity

Tools for the examples and counterexamples of SLP §15.4, pp. 463–467, on `S = ℓ∞ = BddSeq ℝ`.

* `halfSum` : the discounted sum `σ(x) = Σ_t (1/2)ᵗ x_t`, a continuous linear functional on `ℓ∞`
  with no weight at infinity: `σ(xᵀ) → σ(x)` (`tendsto_halfSum_seqTrunc`).
* `tailDist x` : the distance from `x` to the eventually zero sequences `seqC00`; it is convex
  (`tailDist_convex`), `1`-Lipschitz, zero on `seqC00`, eventually at least the size of the
  coordinates (`eventually_norm_lt_tailDist_add`), and `tailDist 1 = 1` (`tailDist_oneSeq`).
  (It equals `limsup_t ‖x_t‖`.)
* `exists_seq_functional_at_infinity` (Hahn–Banach): there is `φ ∈ (ℓ∞)*` with `‖φ‖ ≤ 1`,
  `φ = 0` on `seqC00`, `φ(1) = 1`; such a `φ` is positive (`seq_apply_nonpos_of_nonpos`) and its
  regular part (Lemma 15.5) is zero (`seqRegularPart_eq_zero_of_seqC00`): all of its weight is at
  infinity.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Metric
open scoped ENNReal

/-! ### The discounted sum `σ(x) = Σ (1/2)ᵗ x_t` -/

/-- `Σ_t |(1/2)ᵗ x_t|` converges. -/
theorem summable_half_mul (x : BddSeq ℝ) : Summable fun t => |(1 / 2 : ℝ) ^ t * x t| := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun t => ?_)
    ((summable_geometric_two).mul_right ‖x‖)
  rw [abs_mul, abs_of_nonneg (by positivity), one_div, inv_pow]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_seq_coord_le x t) (by positivity)

/-- `σ` as a linear map. -/
noncomputable def halfSumLinear : BddSeq ℝ →ₗ[ℝ] ℝ where
  toFun x := ∑' t, (1 / 2 : ℝ) ^ t * x t
  map_add' x y := by
    have h : ∀ t, (1 / 2 : ℝ) ^ t * (x + y) t = (1 / 2) ^ t * x t + (1 / 2) ^ t * y t :=
      fun t => by rw [lp.coeFn_add, Pi.add_apply, mul_add]
    simp only [h]
    exact (summable_half_mul x).of_abs.tsum_add (summable_half_mul y).of_abs
  map_smul' c x := by
    have h : ∀ t, (1 / 2 : ℝ) ^ t * (c • x) t = c * ((1 / 2) ^ t * x t) := fun t => by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring
    simp only [h, RingHom.id_apply, smul_eq_mul]
    exact tsum_mul_left

/-- `|σ(x)| ≤ 2 ‖x‖`. -/
theorem norm_halfSumLinear_le (x : BddSeq ℝ) : ‖halfSumLinear x‖ ≤ 2 * ‖x‖ := by
  change |∑' t, (1 / 2 : ℝ) ^ t * x t| ≤ 2 * ‖x‖
  have h := norm_tsum_le_tsum_norm (f := fun t => (1 / 2 : ℝ) ^ t * x t)
    (by simpa only [Real.norm_eq_abs] using summable_half_mul x)
  simp only [Real.norm_eq_abs] at h
  refine h.trans ?_
  have hb : ∀ t, |(1 / 2 : ℝ) ^ t * x t| ≤ (1 / 2) ^ t * ‖x‖ := fun t => by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (by simpa using norm_seq_coord_le x t) (by positivity)
  calc ∑' t, |(1 / 2 : ℝ) ^ t * x t| ≤ ∑' t, (1 / 2 : ℝ) ^ t * ‖x‖ :=
        (summable_half_mul x).tsum_le_tsum hb
          ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _)
    _ = 2 * ‖x‖ := by rw [tsum_mul_right, tsum_geometric_two]

/-- The **discounted sum** `σ(x) = Σ_t (1/2)ᵗ x_t` on `ℓ∞`. -/
noncomputable def halfSum : StrongDual ℝ (BddSeq ℝ) :=
  halfSumLinear.mkContinuous 2 norm_halfSumLinear_le

/-- Value of `σ`. -/
theorem halfSum_apply (x : BddSeq ℝ) : halfSum x = ∑' t, (1 / 2 : ℝ) ^ t * x t := rfl

/-- `σ(x) = Σ_t (1/2)ᵗ x_t` as a `HasSum`. -/
theorem hasSum_halfSum (x : BddSeq ℝ) : HasSum (fun t => (1 / 2 : ℝ) ^ t * x t) (halfSum x) :=
  (summable_half_mul x).of_abs.hasSum

/-- The coordinate functionals of `σ` are `a ↦ (1/2)ᵗ a`. -/
theorem halfSum_single (t : ℕ) (a : ℝ) : halfSum (lp.single ∞ t a) = (1 / 2 : ℝ) ^ t * a := by
  rw [halfSum_apply, tsum_eq_single t]
  · rw [lp.single_apply, Pi.single_eq_same]
  · intro s hs
    rw [lp.single_apply, Pi.single_eq_of_ne hs, mul_zero]

/-- `σ` has no weight at infinity: `σ(xᵀ) → σ(x)`. -/
theorem tendsto_halfSum_seqTrunc (x : BddSeq ℝ) :
    Tendsto (fun T => halfSum (seqTrunc T x)) atTop (𝓝 (halfSum x)) := by
  have h : ∀ T, halfSum (seqTrunc T x) = ∑ t ∈ Finset.range (T + 1), (1 / 2 : ℝ) ^ t * x t :=
    fun T => by
      rw [apply_seqTrunc_eq_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [coordFunctional_apply, halfSum_single]
  simp only [h]
  exact (hasSum_halfSum x).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-! ### The tail distance -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **tail distance** `d(x) = inf {‖x − m‖ : m eventually zero}` (`= limsup_t ‖x_t‖`). -/
noncomputable def tailDist (x : BddSeq E) : ℝ := infDist x (seqC00 E : Set (BddSeq E))

/-- `seqC00` is nonempty. -/
theorem seqC00_nonempty : (seqC00 E : Set (BddSeq E)).Nonempty := ⟨0, (seqC00 E).zero_mem⟩

/-- `d ≥ 0`. -/
theorem tailDist_nonneg (x : BddSeq E) : 0 ≤ tailDist x := infDist_nonneg

/-- `d` vanishes on `seqC00`. -/
theorem tailDist_of_mem {x : BddSeq E} (hx : x ∈ seqC00 E) : tailDist x = 0 :=
  infDist_zero_of_mem hx

/-- `d` is continuous. -/
theorem continuous_tailDist : Continuous (tailDist (E := E)) := continuous_infDist_pt _

/-- `d` is convex. -/
theorem tailDist_convex (x x' : BddSeq E) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    tailDist (θ • x + (1 - θ) • x') ≤ θ * tailDist x + (1 - θ) * tailDist x' := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨m, hm, hdm⟩ := (infDist_lt_iff seqC00_nonempty).1
    (lt_add_of_pos_right (tailDist x) hε)
  obtain ⟨m', hm', hdm'⟩ := (infDist_lt_iff seqC00_nonempty).1
    (lt_add_of_pos_right (tailDist x') hε)
  have hmem : θ • m + (1 - θ) • m' ∈ seqC00 E :=
    (seqC00 E).add_mem ((seqC00 E).smul_mem θ hm) ((seqC00 E).smul_mem (1 - θ) hm')
  have h1θ : 0 ≤ 1 - θ := by linarith
  calc tailDist (θ • x + (1 - θ) • x')
      ≤ dist (θ • x + (1 - θ) • x') (θ • m + (1 - θ) • m') := infDist_le_dist_of_mem hmem
    _ ≤ θ * dist x m + (1 - θ) * dist x' m' := by
        rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
        calc ‖θ • x + (1 - θ) • x' - (θ • m + (1 - θ) • m')‖
            = ‖θ • (x - m) + (1 - θ) • (x' - m')‖ := by
              congr 1; simp only [smul_sub]; abel
          _ ≤ ‖θ • (x - m)‖ + ‖(1 - θ) • (x' - m')‖ := norm_add_le _ _
          _ = θ * ‖x - m‖ + (1 - θ) * ‖x' - m'‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg h0, Real.norm_of_nonneg h1θ]
    _ ≤ θ * (tailDist x + ε) + (1 - θ) * (tailDist x' + ε) := by
        gcongr
    _ = θ * tailDist x + (1 - θ) * tailDist x' + ε := by ring

/-- The coordinates are eventually at most `d(x) + ε`. -/
theorem eventually_norm_lt_tailDist_add (x : BddSeq E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ‖x T‖ < tailDist x + ε := by
  obtain ⟨m, hm, hdm⟩ := (infDist_lt_iff seqC00_nonempty).1
    (lt_add_of_pos_right (tailDist x) hε)
  filter_upwards [hm] with T hT
  calc ‖x T‖ = ‖(x - m) T‖ := by rw [lp.coeFn_sub, Pi.sub_apply, hT, sub_zero]
    _ ≤ ‖x - m‖ := norm_seq_coord_le _ T
    _ = dist x m := (dist_eq_norm x m).symm
    _ < tailDist x + ε := hdm

/-- `d(1) = 1`. -/
theorem tailDist_oneSeq : tailDist oneSeq = 1 := by
  refine le_antisymm ?_ ?_
  · calc tailDist oneSeq ≤ dist oneSeq 0 := infDist_le_dist_of_mem (seqC00 ℝ).zero_mem
      _ = ‖oneSeq‖ := dist_zero_right _
      _ ≤ 1 := norm_oneSeq_le
  · refine (le_infDist seqC00_nonempty).2 fun m hm => ?_
    obtain ⟨t, ht⟩ := (hm : ∀ᶠ t in atTop, m t = 0).exists
    calc (1 : ℝ) = ‖(oneSeq - m) t‖ := by
          rw [lp.coeFn_sub, Pi.sub_apply, ht, sub_zero]; simp [oneSeq]
      _ ≤ ‖oneSeq - m‖ := norm_seq_coord_le _ t
      _ = dist oneSeq m := (dist_eq_norm _ _).symm

/-! ### A functional with all its weight at infinity -/

/-- The quotient norm is the distance to the subspace. -/
theorem norm_quotient_seqC00_mk (x : BddSeq ℝ) :
    ‖(Submodule.Quotient.mk x : BddSeq ℝ ⧸ seqC00 ℝ)‖ = tailDist x :=
  QuotientAddGroup.norm_mk (S := (seqC00 ℝ).toAddSubgroup) x

/-- **A functional at infinity** (Hahn–Banach): some `φ ∈ (ℓ∞)*` has `‖φ‖ ≤ 1`, vanishes on the
eventually zero sequences, and has `φ(1) = 1`. -/
theorem exists_seq_functional_at_infinity :
    ∃ φ : StrongDual ℝ (BddSeq ℝ), ‖φ‖ ≤ 1 ∧ (∀ x ∈ seqC00 ℝ, φ x = 0) ∧ φ oneSeq = 1 := by
  obtain ⟨g, hg1, hgx⟩ :=
    exists_dual_vector'' ℝ (Submodule.Quotient.mk oneSeq : BddSeq ℝ ⧸ seqC00 ℝ)
  have hb : ∀ y : BddSeq ℝ, ‖(g.toLinearMap.comp (seqC00 ℝ).mkQ) y‖ ≤ 1 * ‖y‖ := fun y => by
    change ‖g (Submodule.Quotient.mk y)‖ ≤ 1 * ‖y‖
    calc ‖g (Submodule.Quotient.mk y)‖ ≤ ‖g‖ * ‖(Submodule.Quotient.mk y : BddSeq ℝ ⧸ seqC00 ℝ)‖ :=
          g.le_opNorm _
      _ ≤ 1 * ‖y‖ := mul_le_mul hg1 (Submodule.Quotient.norm_mk_le (seqC00 ℝ) y) (norm_nonneg _)
          zero_le_one
  refine ⟨(g.toLinearMap.comp (seqC00 ℝ).mkQ).mkContinuous 1 hb,
    LinearMap.mkContinuous_norm_le _ zero_le_one hb, fun y hy => ?_, ?_⟩
  · change g (Submodule.Quotient.mk y) = 0
    rw [(Submodule.Quotient.mk_eq_zero (seqC00 ℝ)).2 hy, map_zero]
  · change g (Submodule.Quotient.mk oneSeq) = 1
    rw [hgx, norm_quotient_seqC00_mk, tailDist_oneSeq]
    simp

/-- A functional with `‖φ‖ ≤ 1` and `φ(1) = 1` is positive: `y ≤ 0` implies `φ(y) ≤ 0`. -/
theorem seq_apply_nonpos_of_nonpos {φ : StrongDual ℝ (BddSeq ℝ)} (hφ1 : ‖φ‖ ≤ 1)
    (hφone : φ oneSeq = 1) {y : BddSeq ℝ} (hy : ∀ t, y t ≤ 0) : φ y ≤ 0 := by
  rcases (norm_nonneg y).eq_or_lt with h0 | hpos
  · rw [norm_eq_zero.1 h0.symm, map_zero]
  set M := ‖y‖ with hM
  have hz : ‖oneSeq + M⁻¹ • y‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one fun t => by
    have hyt : |y t| ≤ M := by simpa using norm_seq_coord_le y t
    have h1 : -M ≤ y t := (abs_le.1 hyt).1
    have hv : (oneSeq + M⁻¹ • y) t = 1 + M⁻¹ * y t := by
      rw [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; simp [oneSeq]
    rw [hv, Real.norm_eq_abs, abs_le]
    have h2 : M⁻¹ * y t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hpos.le) (hy t)
    have h3 : -1 ≤ M⁻¹ * y t := by
      rw [le_inv_mul_iff₀ hpos]; linarith
    constructor <;> linarith
  have h := (le_abs_self _).trans ((φ.le_opNorm _).trans
    ((mul_le_mul hφ1 hz (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)))
  rw [map_add, map_smul, hφone, smul_eq_mul] at h
  by_contra hc
  have := mul_pos (inv_pos.2 hpos) (not_le.1 hc)
  linarith [le_abs_self (1 + M⁻¹ * φ y)]

/-- A functional vanishing on `seqC00` has zero regular part (Lemma 15.5): all its weight is at
infinity. -/
theorem seqRegularPart_eq_zero_of_seqC00 {φ : StrongDual ℝ (BddSeq E)}
    (hφ : ∀ x ∈ seqC00 E, φ x = 0) :
    seqRegularPart φ = 0 := by
  ext x
  rw [seqRegularPart_apply, zero_apply]
  refine (tsum_congr fun t => ?_).trans tsum_zero
  rw [coordFunctional_apply]
  refine hφ _ ((eventually_gt_atTop t).mono fun s hs => ?_)
  rw [lp.single_apply, Pi.single_eq_of_ne (ne_of_gt hs)]

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Theorem 15.6: supporting prices without weight at infinity

SLP §15.4, pp. 466–467. The commodity space is `S = BddSeq E`; `ψ = seqRegularPart φ` is the
regular part of `φ ∈ S*` given by Lemma 15.5, `ψ(x) = lim_T φ(xᵀ) = Σ_t ψ_t(x_t)`.

* **Theorem 15.6** (`theorem_15_6`, p. 466): let `[(xᵢ⁰), (yⱼ⁰)]` be feasible, let
  Assumptions 15.1, 15.2, 15.6 and 15.7 hold, let `φ ∈ S*` satisfy
  (4) `x ∈ Xᵢ, uᵢ(x) ≥ uᵢ(xᵢ⁰) ⇒ φ(x) ≥ φ(xᵢ⁰)` and (5) `y ∈ Yⱼ ⇒ φ(y) ≤ φ(yⱼ⁰)`, and let every
  consumer have `x̂ᵢ ∈ Xᵢ` with `uᵢ(x̂ᵢ) > uᵢ(xᵢ⁰)`. Then (4) and (5) hold for `ψ`, and
  `ψ(xᵢ⁰) = φ(xᵢ⁰)`, `ψ(yⱼ⁰) = φ(yⱼ⁰)`. Steps 1 and 2 of the proof are
  `seq_support_step1_consumer`, `seq_support_step1_firm` and `seq_support_step2`.
* `theorem_15_6_of_supporting`: the same with the conclusion of Theorem 15.4 as hypothesis — a
  Pareto optimum and `φ ≠ 0` with (3)–(4) of Theorem 15.4 — giving `ψ` with (3)–(4), no weight at
  infinity, and the inner-product form `ψ(x) = Σ_t ψ_t(x_t)`. It composes with Theorem 15.4.
* `theorem_15_6_competitiveEq`: if in addition 15.3 holds and every consumer has a `ψ`-cheaper
  point (the Remark after Theorem 15.4, applied to `ψ`), then `[(xᵢ⁰), (yⱼ⁰), ψ]` is a competitive
  equilibrium, and `ψ ≠ 0` (`seqRegularPart_ne_zero_of_cheaper`).

**Corrections.**
* Theorem 15.6 does not assert `ψ ≠ 0`, and `ψ = 0` can happen (`theorem_15_6_counterexample`):
  in an economy satisfying all of Assumptions 15.1–15.7 (`S = ℓ∞`, one consumer with
  `X = c00`, `u(x) = Σ_t (1/2)ᵗ x_t`, one firm with `Y = {y ≤ 0}`), the Pareto optimum `0` with a
  nonsatiated consumer is supported by some `φ ≠ 0` (Theorem 15.4's conclusion) whose regular part
  is `ψ = 0`, although a nonzero price system without weight at infinity (`σ = u`) also supports
  it. So "ψ is an equilibrium price system" needs the cheaper-point condition for `ψ`, which the
  book adds in its summary.
* The proof's claim "by 15.1 and 15.2, `uᵢ(x^θ) > uᵢ(xᵢ⁰)`" needs care when `uᵢ(x̂ᵢ) = uᵢ(x)`;
  the transcription's NOTE repairs it with quasi-concavity from 15.3. A case split avoids 15.3
  altogether: if `uᵢ(x) > uᵢ(xᵢ⁰)` apply 15.6–15.7 to `x` itself; if `uᵢ(x) = uᵢ(xᵢ⁰)` then
  `uᵢ(x̂ᵢ) > uᵢ(x)` and 15.2 applies. Assumptions 15.3–15.5 are not used (except 15.3 for the
  equilibrium corollary).
* The nonsatiation point `x̂ᵢ` is needed for every consumer `i`, not just one as in
  Theorem 15.4.
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `θ x̂ + (1 − θ) x → x` as `θ → 0⁺`, staying in `A` for `θ ∈ (0, 1)`. -/
theorem seq_tendsto_segment {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] {A : Set S}
    (hA : Convex ℝ A) {a b : S} (ha : a ∈ A) (hb : b ∈ A) :
    Tendsto (fun θ : ℝ => θ • a + (1 - θ) • b) (𝓝[>] 0) (𝓝[A] b) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : Continuous fun θ : ℝ => θ • a + (1 - θ) • b :=
      (continuous_id.smul continuous_const).add ((continuous_const.sub continuous_id).smul
        continuous_const)
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with θ hθ
    exact hA ha hb hθ.1.le (by linarith [hθ.2]) (by ring)

/-- **Theorem 15.6, Step 1, consumers** ((6), p. 466): `x ∈ Xᵢ`, `uᵢ(x) ≥ uᵢ(xᵢ⁰)` imply
`ψ(x) ≥ φ(xᵢ⁰)`. Uses 15.1, 15.2, 15.6, 15.7 and the nonsatiation point `x̂ᵢ` (not 15.3). -/
theorem seq_support_step1_consumer {A : Set (BddSeq E)} {v : BddSeq E → ℝ}
    {φ : StrongDual ℝ (BddSeq E)} {x₀ : BddSeq E} (hA : Convex ℝ A) (hqc : SeqSemistrictQC A v)
    (htc : SeqTruncClosed A) (hti : SeqTailInsensitive A v) (hx₀ : x₀ ∈ A)
    (hsup : ∀ z ∈ A, v x₀ ≤ v z → φ x₀ ≤ φ z) {xh : BddSeq E} (hxh : xh ∈ A)
    (hns : v x₀ < v xh) : ∀ z ∈ A, v x₀ ≤ v z → φ x₀ ≤ seqRegularPart φ z := by
  have key : ∀ w ∈ A, v x₀ < v w → φ x₀ ≤ seqRegularPart φ w := fun w hw hlt =>
    ge_of_tendsto (tendsto_apply_seqTrunc φ w)
      ((hti.eventually htc hw hx₀ hlt).mono fun _ hT => hsup _ hT.1 hT.2.le)
  intro z hz hle
  rcases hle.lt_or_eq with hlt | heq
  · exact key z hz hlt
  · have hzxh : v z < v xh := heq ▸ hns
    have hlim : Tendsto (fun θ : ℝ => θ * seqRegularPart φ xh + (1 - θ) * seqRegularPart φ z)
        (𝓝[>] 0) (𝓝 (seqRegularPart φ z)) := by
      have hc : Continuous fun θ : ℝ =>
          θ * seqRegularPart φ xh + (1 - θ) * seqRegularPart φ z :=
        (continuous_id.mul continuous_const).add ((continuous_const.sub continuous_id).mul
          continuous_const)
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with θ hθ
    have hmem : θ • xh + (1 - θ) • z ∈ A := hA hxh hz hθ.1.le (by linarith [hθ.2]) (by ring)
    have hv : v x₀ < v (θ • xh + (1 - θ) • z) := heq ▸ hqc xh hxh z hz hzxh θ hθ.1 hθ.2
    have := key _ hmem hv
    rwa [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this

/-- **Theorem 15.6, Step 1, firms** ((7), p. 466): `y ∈ Yⱼ` implies `ψ(y) ≤ φ(yⱼ⁰)`. -/
theorem seq_support_step1_firm {B : Set (BddSeq E)} {φ : StrongDual ℝ (BddSeq E)}
    {y₀ : BddSeq E} (htc : SeqTruncClosed B) (hsup : ∀ w ∈ B, φ w ≤ φ y₀) :
    ∀ w ∈ B, seqRegularPart φ w ≤ φ y₀ := fun w hw =>
  le_of_tendsto (tendsto_apply_seqTrunc φ w) ((htc w hw).mono fun _ hT => hsup _ hT)

/-- **Theorem 15.6, Step 2** (p. 467): from `ψ(xᵢ⁰) ≥ φ(xᵢ⁰)`, `ψ(yⱼ⁰) ≤ φ(yⱼ⁰)` and
`Σᵢ xᵢ⁰ = Σⱼ yⱼ⁰`, all these inequalities are equalities. -/
theorem seq_support_step2 {ι κ : Type*} [Fintype ι] [Fintype κ] {φ ψ : StrongDual ℝ (BddSeq E)}
    {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E} (hfeas : ∑ i, x₀ i - ∑ j, y₀ j = 0)
    (hx : ∀ i, φ (x₀ i) ≤ ψ (x₀ i)) (hy : ∀ j, ψ (y₀ j) ≤ φ (y₀ j)) :
    (∀ i, ψ (x₀ i) = φ (x₀ i)) ∧ ∀ j, ψ (y₀ j) = φ (y₀ j) := by
  have hsum : ∑ i, x₀ i = ∑ j, y₀ j := sub_eq_zero.1 hfeas
  have htot : ∑ i, (ψ (x₀ i) - φ (x₀ i)) + ∑ j, (φ (y₀ j) - ψ (y₀ j)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← map_sum, ← map_sum, ← map_sum,
      ← map_sum, hsum]
    ring
  have ha : ∀ i ∈ Finset.univ, 0 ≤ ψ (x₀ i) - φ (x₀ i) := fun i _ => sub_nonneg.2 (hx i)
  have hb : ∀ j ∈ Finset.univ, 0 ≤ φ (y₀ j) - ψ (y₀ j) := fun j _ => sub_nonneg.2 (hy j)
  have hA0 := Finset.sum_nonneg ha
  have hB0 := Finset.sum_nonneg hb
  have hA : ∑ i, (ψ (x₀ i) - φ (x₀ i)) = 0 := by linarith
  have hB : ∑ j, (φ (y₀ j) - ψ (y₀ j)) = 0 := by linarith
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have := (Finset.sum_eq_zero_iff_of_nonneg ha).1 hA i (Finset.mem_univ i)
    linarith
  · have := (Finset.sum_eq_zero_iff_of_nonneg hb).1 hB j (Finset.mem_univ j)
    linarith

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Theorem 15.6** (p. 466). Let `[(xᵢ⁰), (yⱼ⁰)]` be feasible, let Assumptions 15.1, 15.2, 15.6
and 15.7 hold, let `φ ∈ S*` satisfy (4) and (5), and let every consumer `i` have `x̂ᵢ ∈ Xᵢ` with
`uᵢ(x̂ᵢ) > uᵢ(xᵢ⁰)`. Then `ψ = seqRegularPart φ` (Lemma 15.5) satisfies (4) and (5), and agrees
with `φ` on every `xᵢ⁰` and `yⱼ⁰`. (Assumptions 15.3–15.5 are not needed.) -/
theorem theorem_15_6 {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ} {Y : κ → Set (BddSeq E)}
    {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E} (h1 : Assumption15_1 X) (h2 : Assumption15_2 X u)
    (h6 : Assumption15_6 X Y) (h7 : Assumption15_7 X u) (hfeas : Feasible X Y x₀ y₀)
    (φ : StrongDual ℝ (BddSeq E))
    (h4 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z)
    (h5 : ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j))
    (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh) :
    (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → seqRegularPart φ (x₀ i) ≤ seqRegularPart φ z) ∧
    (∀ j, ∀ w ∈ Y j, seqRegularPart φ w ≤ seqRegularPart φ (y₀ j)) ∧
    (∀ i, seqRegularPart φ (x₀ i) = φ (x₀ i)) ∧ ∀ j, seqRegularPart φ (y₀ j) = φ (y₀ j) := by
  have s6 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ seqRegularPart φ z := fun i => by
    obtain ⟨xh, hxh, hlt⟩ := hns i
    exact seq_support_step1_consumer (h1 i) (h2 i) (h6.1 i) (h7 i) (hfeas.1 i) (h4 i) hxh hlt
  have s7 : ∀ j, ∀ w ∈ Y j, seqRegularPart φ w ≤ φ (y₀ j) := fun j =>
    seq_support_step1_firm (h6.2 j) (h5 j)
  obtain ⟨ex, ey⟩ := seq_support_step2 (φ := φ) (ψ := seqRegularPart φ) hfeas.2.2
    (fun i => s6 i _ (hfeas.1 i) le_rfl) (fun j => s7 j _ (hfeas.2.1 j))
  exact ⟨fun i z hz hle => (ex i).trans_le (s6 i z hz hle),
    fun j w hw => (s7 j w hw).trans_eq (ey j).symm, ex, ey⟩

/-- **Theorem 15.6, composed with the conclusion of Theorem 15.4.** For a Pareto optimum
satisfying 15.1, 15.2, 15.6 and 15.7 with every consumer nonsatiated, if some `φ ∈ S*`, `φ ≠ 0`,
satisfies (3)–(4) of Theorem 15.4, then some `ψ ∈ S*` satisfies (3)–(4), has no weight at infinity
(`ψ(x) = lim_T ψ(xᵀ)`) and has the inner-product form `ψ(x) = Σ_t ψ_t(x_t)`. (It need not be
nonzero: `theorem_15_6_counterexample`.) -/
theorem theorem_15_6_of_supporting {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ}
    {Y : κ → Set (BddSeq E)} {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E} (h1 : Assumption15_1 X)
    (h2 : Assumption15_2 X u) (h6 : Assumption15_6 X Y) (h7 : Assumption15_7 X u)
    (hPO : ParetoOptimal X u Y x₀ y₀) (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh)
    (hφ : ∃ φ : StrongDual ℝ (BddSeq E), φ ≠ 0 ∧
      (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z) ∧
      ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j)) :
    ∃ ψ : StrongDual ℝ (BddSeq E),
      (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → ψ (x₀ i) ≤ ψ z) ∧
      (∀ j, ∀ w ∈ Y j, ψ w ≤ ψ (y₀ j)) ∧
      (∀ x, Tendsto (fun T => ψ (seqTrunc T x)) atTop (𝓝 (ψ x))) ∧
      ∀ x : BddSeq E, HasSum (fun t => coordFunctional ψ t (x t)) (ψ x) := by
  obtain ⟨φ, -, h3, h4⟩ := hφ
  obtain ⟨r4, r5, -, -⟩ := theorem_15_6 h1 h2 h6 h7 hPO.1 φ h3 h4 hns
  refine ⟨seqRegularPart φ, r4, r5, fun x => ?_, fun x => ?_⟩
  · simpa [seqRegularPart_seqRegularPart] using tendsto_apply_seqTrunc (seqRegularPart φ) x
  · simpa [seqRegularPart_seqRegularPart] using hasSum_seqRegularPart (seqRegularPart φ) x

/-- The Remark after Theorem 15.4 (p. 456), for one consumer: if `ψ` satisfies (3) at `x⁰`,
`u` is continuous on the convex set `A`, and some `w ∈ A` has `ψ(w) < ψ(x⁰)`, then `x⁰` maximises
`u` on the budget set `{z ∈ A : ψ(z) ≤ ψ(x⁰)}`. -/
theorem seq_budget_max_of_cheaper {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {A : Set S} {v : S → ℝ} {ψ : StrongDual ℝ S} {x₀ : S} (hA : Convex ℝ A)
    (hv : ContinuousOn v A) (h3 : ∀ z ∈ A, v x₀ ≤ v z → ψ x₀ ≤ ψ z) {w : S} (hw : w ∈ A)
    (hcheap : ψ w < ψ x₀) : ∀ z ∈ A, ψ z ≤ ψ x₀ → v z ≤ v x₀ := by
  intro z hz hbud
  by_contra hcon
  have hlim := ((hv z hz).tendsto).comp (seq_tendsto_segment hA hw hz)
  obtain ⟨θ, hθ, hvθ⟩ := ((show ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo 0 1 from
    Ioo_mem_nhdsGT (zero_lt_one' ℝ)).and
    (hlim.eventually (lt_mem_nhds (not_le.1 hcon)))).exists
  have hmem : θ • w + (1 - θ) • z ∈ A := hA hw hz hθ.1.le (by linarith [hθ.2]) (by ring)
  have := h3 _ hmem hvθ.le
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at this
  nlinarith [hθ.1, hθ.2]

/-- **Theorem 15.6 with the Remark**: under the hypotheses of `theorem_15_6`, Assumption 15.3, and
a `ψ`-cheaper point `x′ᵢ ∈ Xᵢ` (`ψ(x′ᵢ) < ψ(xᵢ⁰)`) for every consumer, `[(xᵢ⁰), (yⱼ⁰), ψ]` is a
competitive equilibrium with a price system without weight at infinity. -/
theorem theorem_15_6_competitiveEq {X : ι → Set (BddSeq E)} {u : ι → BddSeq E → ℝ}
    {Y : κ → Set (BddSeq E)} {x₀ : ι → BddSeq E} {y₀ : κ → BddSeq E} (h1 : Assumption15_1 X)
    (h2 : Assumption15_2 X u) (h3 : Assumption15_3 X u) (h6 : Assumption15_6 X Y)
    (h7 : Assumption15_7 X u) (hfeas : Feasible X Y x₀ y₀) (φ : StrongDual ℝ (BddSeq E))
    (h4 : ∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z)
    (h5 : ∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j))
    (hns : ∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh)
    (hcheap : ∀ i, ∃ w ∈ X i, seqRegularPart φ w < seqRegularPart φ (x₀ i)) :
    CompetitiveEq X u Y x₀ y₀ (seqRegularPart φ) := by
  obtain ⟨r4, r5, -, -⟩ := theorem_15_6 h1 h2 h6 h7 hfeas φ h4 h5 hns
  refine ⟨hfeas, fun i => ?_, r5⟩
  obtain ⟨w, hw, hlt⟩ := hcheap i
  exact seq_budget_max_of_cheaper (h1 i) (h3 i) (r4 i) hw hlt

/-- With a cheaper point for some consumer, `ψ ≠ 0`. -/
theorem seqRegularPart_ne_zero_of_cheaper {φ : StrongDual ℝ (BddSeq E)} {w x : BddSeq E}
    (h : seqRegularPart φ w < seqRegularPart φ x) : seqRegularPart φ ≠ 0 := fun h0 => by
  rw [h0] at h
  simp at h

/-! ### `ψ` can vanish -/

/-- `σ(y) ≤ 0` for `y ≤ 0`. -/
theorem halfSum_nonpos {y : BddSeq ℝ} (hy : ∀ t, y t ≤ 0) : halfSum y ≤ 0 :=
  tsum_nonpos fun t => mul_nonpos_of_nonneg_of_nonpos (by positivity) (hy t)

/-- **Theorem 15.6 does not give `ψ ≠ 0`.** On `S = ℓ∞`, take one consumer with `X = c00` and
`u = σ` (`σ(x) = Σ_t (1/2)ᵗ x_t`), one firm with `Y = {y : y_t ≤ 0 ∀ t}`, and the allocation
`x⁰ = y⁰ = 0`. Assumptions 15.1–15.7 hold, the allocation is Pareto optimal, the consumer is
nonsatiated, and some `φ ≠ 0` satisfies (3)–(4) of Theorem 15.4, but its regular part is `ψ = 0`.
Yet `σ ≠ 0`, which has no weight at infinity, also satisfies (3)–(4). -/
theorem theorem_15_6_counterexample :
    ∃ (X : Unit → Set (BddSeq ℝ)) (u : Unit → BddSeq ℝ → ℝ) (Y : Unit → Set (BddSeq ℝ))
      (x₀ : Unit → BddSeq ℝ) (y₀ : Unit → BddSeq ℝ) (φ : StrongDual ℝ (BddSeq ℝ)),
      Assumption15_1 X ∧ Assumption15_2 X u ∧ Assumption15_3 X u ∧ Assumption15_4 Y ∧
      Assumption15_5 (BddSeq ℝ) Y ∧ Assumption15_6 X Y ∧ Assumption15_7 X u ∧
      ParetoOptimal X u Y x₀ y₀ ∧ (∀ i, ∃ xh ∈ X i, u i (x₀ i) < u i xh) ∧
      φ ≠ 0 ∧ (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → φ (x₀ i) ≤ φ z) ∧
      (∀ j, ∀ w ∈ Y j, φ w ≤ φ (y₀ j)) ∧ seqRegularPart φ = 0 ∧
      (halfSum ≠ 0 ∧ (∀ i, ∀ z ∈ X i, u i (x₀ i) ≤ u i z → halfSum (x₀ i) ≤ halfSum z) ∧
        (∀ j, ∀ w ∈ Y j, halfSum w ≤ halfSum (y₀ j)) ∧ seqRegularPart halfSum = halfSum) := by
  obtain ⟨φ, hφ1, hφ0, hφone⟩ := exists_seq_functional_at_infinity
  set Ycone : Set (BddSeq ℝ) := {y | ∀ t, y t ≤ 0} with hYcone
  have hagg : aggTech (fun _ : Unit => Ycone) = Ycone := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy ()
    · intro hw
      exact ⟨fun _ => w, fun _ => hw, by simp⟩
  have hYconv : Convex ℝ Ycone := fun y hy y' hy' a b ha hb _ t => by
    rw [seq_coord_combo, smul_eq_mul, smul_eq_mul]
    nlinarith [hy t, hy' t]
  have hsingle : halfSum (lp.single ∞ 0 1) = 1 := by rw [halfSum_single]; norm_num
  refine ⟨fun _ => (seqC00 ℝ : Set (BddSeq ℝ)), fun _ => halfSum, fun _ => Ycone, fun _ => 0,
    fun _ => 0, φ, fun _ => (seqC00 ℝ).convex, fun _ z _ z' _ hlt θ h0 h1 => ?_,
    fun _ => halfSum.continuous.continuousOn, ?_, ?_, ⟨fun _ x hx => ?_, fun _ y hy => ?_⟩,
    fun _ => SeqTailInsensitive.of_tendsto fun x _ => tendsto_halfSum_seqTrunc x, ⟨⟨fun _ => ?_,
    fun _ => ?_, by simp⟩, ?_⟩, fun _ => ⟨lp.single ∞ 0 1, ?_, ?_⟩, ?_, fun _ z hz _ => ?_,
    fun _ w hw => ?_, seqRegularPart_eq_zero_of_seqC00 hφ0, ?_, fun _ z _ hz => hz,
    fun _ w hw => ?_, ?_⟩
  · change halfSum z' < halfSum z at hlt
    change halfSum z' < halfSum (θ • z + (1 - θ) • z')
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    nlinarith
  · change Convex ℝ (aggTech fun _ : Unit => Ycone)
    rw [hagg]; exact hYconv
  · left
    rw [hagg]
    refine ⟨-oneSeq, mem_interior.2 ⟨Metric.ball (-oneSeq) 1, fun y hy t => ?_,
      Metric.isOpen_ball, Metric.mem_ball_self one_pos⟩⟩
    have h := (norm_seq_coord_le (y - -oneSeq) t).trans_lt (by rwa [← dist_eq_norm])
    rw [lp.coeFn_sub, lp.coeFn_neg, Pi.sub_apply, Pi.neg_apply] at h
    have h' := (abs_lt.1 (by simpa using h)).2
    simp [oneSeq] at h'
    linarith
  · exact Eventually.of_forall fun T => seqTrunc_mem_seqC00 T x
  · refine Eventually.of_forall fun T t => ?_
    rw [seqTrunc_apply]; split_ifs
    · exact hy t
    · exact le_rfl
  · exact (seqC00 ℝ).zero_mem
  · exact fun t => le_rfl
  · rintro ⟨x', y', ⟨hx', hy', hxy⟩, -, i, hi⟩
    simp only [Finset.univ_unique, Finset.sum_singleton] at hxy
    have he : x' () = y' () := sub_eq_zero.1 hxy
    have := halfSum_nonpos (y := x' ()) fun t => he ▸ hy' () t
    simp only [map_zero] at hi
    exact absurd hi (not_lt.2 (by cases i; exact this))
  · exact (eventually_gt_atTop 0).mono fun s hs => by
      rw [lp.single_apply, Pi.single_eq_of_ne (ne_of_gt hs)]
  · simp [hsingle]
  · intro h0
    have := congrArg (fun f : StrongDual ℝ (BddSeq ℝ) => f oneSeq) h0
    simp [hφone] at this
  · simp [hφ0 z hz]
  · simp [seq_apply_nonpos_of_nonpos hφ1 hφone hw]
  · intro h0
    have := congrArg (fun f : StrongDual ℝ (BddSeq ℝ) => f (lp.single ∞ 0 1)) h0
    simp [hsingle] at this
  · simpa using halfSum_nonpos hw
  · ext x
    exact tendsto_nhds_unique (tendsto_apply_seqTrunc halfSum x) (tendsto_halfSum_seqTrunc x)

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Exercise 15.11: Assumption 15.7 and limits of truncated utilities

SLP §15.4, p. 465, with `S = ℓ∞ = BddSeq ℝ`.

* **Exercise 15.11(a)** (`ex_15_11a`): `u(x) = inf_t x_t` on `X = {x : 0 ≤ x_t ≤ 1}` violates
  Assumption 15.7 (while `X` satisfies 15.1 and 15.6).
* **Exercise 15.11(b)**, "if" (`ex_15_11b_if`): `u(x) = lim_T u(xᵀ)` for all `x ∈ X` implies 15.7.
* **Exercise 15.11(b)**, corrected (`ex_15_11b_liminf`): if `X` is convex, satisfies 15.6, and `u`
  is continuous on `X`, then 15.7 holds iff `liminf_T u(xᵀ) ≥ u(x)` for every `x ∈ X` (in the
  form: `c < u(x)` implies `c < u(xᵀ)` for all large `T`).

**Corrections.**
* The "only if" of Exercise 15.11(b) is false (`ex_15_11b_counterexample`): on `X = ℓ∞`,
  `u(x) = Σ_t (1/2)ᵗ x_t − d(x)`, `d(x) = dist(x, seqC00) = limsup_t |x_t|`, satisfies 15.1–15.3,
  15.6 and 15.7, but `u(1ᵀ) → 2 ≠ 1 = u(1)`.
* The manual's "partial converse" (15.7 implies that `lim_T u(xᵀ)` exists and is `≥ u(x)`) is
  false (`ex_15_11b_manual_counterexample`): `u(x) = Σ_t (1/2)ᵗ x_t − d(x) − g(x)`, with
  `g(x) = sup_t (x_{2t+1} − x_{2t+2})⁺` (`oddDrop`), satisfies 15.1–15.3, 15.6 and 15.7, but
  `u(1ᵀ)` oscillates (`g(1ᵀ) = 1` for odd `T`, `0` for even `T`). The manual's existence step
  applies 15.7 to the pair `(x^{T̂}, x̂)`, which says nothing about `u(xᵀ)`. The manual's
  inequality `liminf_T u(xᵀ) ≥ u(x)` is correct (`ex_15_11b_liminf`).
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Set
open scoped ENNReal

/-! ### Exercise 15.11(a) -/

/-- The utility `u(x) = inf_t x_t`. -/
noncomputable def infUtility (x : BddSeq ℝ) : ℝ := ⨅ t, x t

/-- **Exercise 15.11(a)**: `u(x) = inf_t x_t` on `X = {x ∈ ℓ∞ : 0 ≤ x_t ≤ 1}` does not satisfy
Assumption 15.7 (`x = 1`, `x′ = 1/2`, `u(xᵀ) = 0`), although `X` satisfies 15.1 and 15.6. -/
theorem ex_15_11a :
    Convex ℝ (seqSet (Icc (0 : ℝ) 1)) ∧ SeqTruncClosed (seqSet (Icc (0 : ℝ) 1)) ∧
    ¬ SeqTailInsensitive (seqSet (Icc (0 : ℝ) 1)) infUtility := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine ⟨(ex_15_10a (convex_Icc 0 1) h0).1, (ex_15_10a (convex_Icc 0 1) h0).2, fun h => ?_⟩
  have hx : oneSeq ∈ seqSet (Icc (0 : ℝ) 1) := fun t => by simp [oneSeq]
  have hx' : (1 / 2 : ℝ) • oneSeq ∈ seqSet (Icc (0 : ℝ) 1) := fun t => by
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; simp [oneSeq]; norm_num
  have hu1 : infUtility oneSeq = 1 := by simp [infUtility, oneSeq]
  have hu2 : infUtility ((1 / 2 : ℝ) • oneSeq) = 1 / 2 := by
    unfold infUtility
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    simp [oneSeq]
  obtain ⟨T, hT⟩ := (h oneSeq hx _ hx' (by rw [hu1, hu2]; norm_num)).exists
  have hmem := seqTrunc_mem_seqSet h0 hx T
  have hle : infUtility (seqTrunc T oneSeq) ≤ 0 := by
    have hb : BddBelow (range fun t => seqTrunc T oneSeq t) :=
      ⟨0, by rintro _ ⟨t, rfl⟩; exact (hmem t).1⟩
    calc infUtility (seqTrunc T oneSeq) ≤ seqTrunc T oneSeq (T + 1) := ciInf_le hb (T + 1)
      _ = 0 := by simp [seqTrunc_apply]
  have := hT hmem
  rw [hu2] at this
  linarith

/-! ### Exercise 15.11(b) -/

/-- **Exercise 15.11(b)**, "if": `u(x) = lim_T u(xᵀ)` for every `x ∈ X` implies 15.7. -/
theorem ex_15_11b_if {A : Set (BddSeq ℝ)} {v : BddSeq ℝ → ℝ}
    (h : ∀ x ∈ A, Tendsto (fun T => v (seqTrunc T x)) atTop (𝓝 (v x))) : SeqTailInsensitive A v :=
  SeqTailInsensitive.of_tendsto h

/-- **Exercise 15.11(b)**, corrected: for `X` convex and closed under truncation far out (15.6),
and `u` continuous on `X`, Assumption 15.7 holds iff `liminf_T u(xᵀ) ≥ u(x)` for all `x ∈ X`.
(The "⇒" is the manual's inequality; the manual's claim that the limit exists is false, see
`ex_15_11b_manual_counterexample`.) -/
theorem ex_15_11b_liminf {A : Set (BddSeq ℝ)} {v : BddSeq ℝ → ℝ} (hA : SeqTruncClosed A)
    (hconv : Convex ℝ A) (hv : ContinuousOn v A) :
    SeqTailInsensitive A v ↔ ∀ x ∈ A, ∀ c < v x, ∀ᶠ T in atTop, c < v (seqTrunc T x) := by
  refine ⟨fun h x hx c hc => ?_, SeqTailInsensitive.of_liminf⟩
  by_cases hmin : ∀ y ∈ A, c < v y
  · exact (hA x hx).mono fun T hT => hmin _ hT
  simp only [not_forall, not_lt, exists_prop] at hmin
  obtain ⟨y, hy, hyc⟩ := hmin
  set g : ℝ → ℝ := fun θ => v (θ • x + (1 - θ) • y) with hg
  have hseg : ∀ θ ∈ Icc (0 : ℝ) 1, θ • x + (1 - θ) • y ∈ A := fun θ hθ =>
    hconv hx hy hθ.1 (by linarith [hθ.2]) (by ring)
  have hgc : ContinuousOn g (Icc 0 1) :=
    hv.comp (((continuous_id.smul continuous_const).add
      ((continuous_const.sub continuous_id).smul continuous_const)).continuousOn) hseg
  have hg0 : g 0 = v y := by simp [hg]
  have hg1 : g 1 = v x := by simp [hg]
  obtain ⟨θ, hθ, hgθ⟩ := intermediate_value_Icc zero_le_one hgc
    (⟨hg0 ▸ hyc, hg1 ▸ hc.le⟩ : c ∈ Icc (g 0) (g 1))
  have hx' := hseg θ hθ
  have hlt : v (θ • x + (1 - θ) • y) < v x := by
    change g θ < v x
    rw [hgθ]; exact hc
  refine ((h x hx _ hx' hlt).and (hA x hx)).mono fun T hT => ?_
  have := hT.1 hT.2
  rwa [show v (θ • x + (1 - θ) • y) = c from hgθ] at this

/-- The utility `u(x) = Σ_t (1/2)ᵗ x_t − d(x)` with `d(x) = dist(x, seqC00) = limsup_t |x_t|`. -/
noncomputable def tailPenalizedUtility (x : BddSeq ℝ) : ℝ := halfSum x - tailDist x

/-- The concavity inequality for `σ − d − f` with `f` convex. -/
theorem concave_halfSum_sub {f : BddSeq ℝ → ℝ}
    (hf : ∀ x x' : BddSeq ℝ, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      f (θ • x + (1 - θ) • x') ≤ θ * f x + (1 - θ) * f x') (x x' : BddSeq ℝ) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ * (halfSum x - tailDist x - f x) + (1 - θ) * (halfSum x' - tailDist x' - f x') ≤
      halfSum (θ • x + (1 - θ) • x') - tailDist (θ • x + (1 - θ) • x') -
        f (θ • x + (1 - θ) • x') := by
  have h1' := tailDist_convex x x' h0 h1
  have h2 := hf x x' θ h0 h1
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  linarith

/-- **The "only if" of Exercise 15.11(b) is false.** On `X = ℓ∞`, `u(x) = Σ_t (1/2)ᵗ x_t − d(x)`
satisfies 15.1, 15.2 (it is concave), 15.3, 15.6 and 15.7, but `u(1ᵀ) ↛ u(1)`. -/
theorem ex_15_11b_counterexample :
    Convex ℝ (univ : Set (BddSeq ℝ)) ∧ SeqTruncClosed (univ : Set (BddSeq ℝ)) ∧
    SeqSemistrictQC univ tailPenalizedUtility ∧ ContinuousOn tailPenalizedUtility univ ∧
    SeqTailInsensitive univ tailPenalizedUtility ∧
    ¬ ∀ x ∈ (univ : Set (BddSeq ℝ)),
      Tendsto (fun T => tailPenalizedUtility (seqTrunc T x)) atTop
        (𝓝 (tailPenalizedUtility x)) := by
  have htr : ∀ x T, tailPenalizedUtility (seqTrunc T x) = halfSum (seqTrunc T x) := fun x T => by
    simp [tailPenalizedUtility, tailDist_of_mem (seqTrunc_mem_seqC00 T x)]
  refine ⟨convex_univ, fun _ _ => Eventually.of_forall fun _ => mem_univ _,
    SeqSemistrictQC.of_concave fun x _ x' _ θ h0 h1 => ?_,
    (halfSum.continuous.sub continuous_tailDist).continuousOn,
    SeqTailInsensitive.of_liminf fun x _ c hc => ?_, fun h => ?_⟩
  · simpa [tailPenalizedUtility] using
      concave_halfSum_sub (f := fun _ => 0) (fun _ _ _ _ _ => by simp) x x' h0.le h1.le
  · have hc' : c < halfSum x := hc.trans_le (sub_le_self _ (tailDist_nonneg x))
    exact ((tendsto_halfSum_seqTrunc x).eventually (lt_mem_nhds hc')).mono fun T hT => by
      rw [htr]; exact hT
  · have h1 := h oneSeq (mem_univ _)
    simp only [htr] at h1
    have h2 := tendsto_nhds_unique (tendsto_halfSum_seqTrunc oneSeq) h1
    rw [tailPenalizedUtility, tailDist_oneSeq] at h2
    linarith

/-- The "odd drop" `g(x) = sup_t (x_{2t+1} − x_{2t+2})⁺`. -/
noncomputable def oddDrop (x : BddSeq ℝ) : ℝ := ⨆ t : ℕ, max 0 (x (2 * t + 1) - x (2 * t + 2))

/-- The terms of `oddDrop` are bounded by `2‖x‖`. -/
theorem oddDrop_term_le_norm (x : BddSeq ℝ) (t : ℕ) :
    max 0 (x (2 * t + 1) - x (2 * t + 2)) ≤ 2 * ‖x‖ := by
  have h1 : |x (2 * t + 1)| ≤ ‖x‖ := by simpa using norm_seq_coord_le x (2 * t + 1)
  have h2 : |x (2 * t + 2)| ≤ ‖x‖ := by simpa using norm_seq_coord_le x (2 * t + 2)
  refine max_le (by positivity) ?_
  linarith [(abs_le.1 h1).2, (abs_le.1 h2).1]

/-- The terms of `oddDrop` are bounded above. -/
theorem oddDrop_bddAbove (x : BddSeq ℝ) :
    BddAbove (range fun t : ℕ => max 0 (x (2 * t + 1) - x (2 * t + 2))) :=
  ⟨2 * ‖x‖, by rintro _ ⟨t, rfl⟩; exact oddDrop_term_le_norm x t⟩

/-- Each term is at most `oddDrop x`. -/
theorem oddDrop_term_le (x : BddSeq ℝ) (t : ℕ) :
    max 0 (x (2 * t + 1) - x (2 * t + 2)) ≤ oddDrop x :=
  le_ciSup (oddDrop_bddAbove x) t

/-- `g ≥ 0`. -/
theorem oddDrop_nonneg (x : BddSeq ℝ) : 0 ≤ oddDrop x :=
  (le_max_left _ _).trans (oddDrop_term_le x 0)

/-- `g` is convex. -/
theorem oddDrop_convex (x x' : BddSeq ℝ) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    oddDrop (θ • x + (1 - θ) • x') ≤ θ * oddDrop x + (1 - θ) * oddDrop x' := by
  refine ciSup_le fun t => ?_
  rw [seq_coord_combo, seq_coord_combo]
  simp only [smul_eq_mul]
  have e1 := oddDrop_term_le x t
  have e2 := oddDrop_term_le x' t
  have h1θ : 0 ≤ 1 - θ := by linarith
  refine max_le (by positivity [oddDrop_nonneg x, oddDrop_nonneg x']) ?_
  have f1 : x (2 * t + 1) - x (2 * t + 2) ≤ oddDrop x := (le_max_right _ _).trans e1
  have f2 : x' (2 * t + 1) - x' (2 * t + 2) ≤ oddDrop x' := (le_max_right _ _).trans e2
  nlinarith [mul_le_mul_of_nonneg_left f1 h0, mul_le_mul_of_nonneg_left f2 h1θ]

/-- `g` is `2`-Lipschitz, hence continuous. -/
theorem continuous_oddDrop : Continuous oddDrop := by
  refine (LipschitzWith.of_le_add_mul 2 fun x y => ?_).continuous
  refine ciSup_le fun t => ?_
  have h1 : |(x - y) (2 * t + 1)| ≤ ‖x - y‖ := by simpa using norm_seq_coord_le (x - y) (2 * t + 1)
  have h2 : |(x - y) (2 * t + 2)| ≤ ‖x - y‖ := by simpa using norm_seq_coord_le (x - y) (2 * t + 2)
  rw [lp.coeFn_sub, Pi.sub_apply] at h1 h2
  have e := oddDrop_term_le y t
  rw [dist_eq_norm]
  refine max_le (by have := oddDrop_nonneg y; positivity) ?_
  have := (le_max_right 0 (y (2 * t + 1) - y (2 * t + 2))).trans e
  push_cast
  linarith [(abs_le.1 h1).2, (abs_le.1 h2).1]

/-- Truncation raises `g` by at most `‖x_T‖`: `g(xᵀ) ≤ g(x) + ‖x_T‖`. -/
theorem oddDrop_seqTrunc_le (x : BddSeq ℝ) (T : ℕ) :
    oddDrop (seqTrunc T x) ≤ oddDrop x + ‖x T‖ := by
  refine ciSup_le fun t => ?_
  simp only [seqTrunc_apply]
  have e := oddDrop_term_le x t
  have hn := norm_nonneg (x T)
  have hg := oddDrop_nonneg x
  by_cases ha : 2 * t + 2 ≤ T
  · simp only [show 2 * t + 1 ≤ T by omega, ha, ↓reduceIte]; linarith
  · simp only [ha, ↓reduceIte]
    by_cases hb : 2 * t + 1 ≤ T
    · simp only [hb, ↓reduceIte]
      have hT : 2 * t + 1 = T := by omega
      rw [hT, sub_zero]
      refine max_le (by positivity) ?_
      linarith [le_abs_self (x T), Real.norm_eq_abs (x T)]
    · simp only [hb, ↓reduceIte, sub_zero, max_self]; positivity

/-- `g(1ᵀ) = 1` for odd `T` and `0` for even `T`. -/
theorem oddDrop_seqTrunc_one (k : ℕ) :
    oddDrop (seqTrunc (2 * k) oneSeq) = 0 ∧ oddDrop (seqTrunc (2 * k + 1) oneSeq) = 1 := by
  have hone : ∀ t, oneSeq t = 1 := fun t => rfl
  constructor
  · refine le_antisymm (ciSup_le fun t => ?_) (oddDrop_nonneg _)
    simp only [seqTrunc_apply, hone]
    refine max_le le_rfl ?_
    split_ifs <;> first | omega | norm_num
  · refine le_antisymm (ciSup_le fun t => ?_) ?_
    · simp only [seqTrunc_apply, hone]
      refine max_le zero_le_one ?_
      split_ifs <;> norm_num
    · refine le_trans ?_ (oddDrop_term_le _ k)
      simp only [seqTrunc_apply, hone]
      simp only [le_refl, show ¬ 2 * k + 2 ≤ 2 * k + 1 by omega, ↓reduceIte]
      norm_num

/-- The utility `u(x) = Σ_t (1/2)ᵗ x_t − d(x) − g(x)`. -/
noncomputable def oscillatingUtility (x : BddSeq ℝ) : ℝ := halfSum x - tailDist x - oddDrop x

/-- **The manual's "partial converse" to Exercise 15.11(b) is false.** On `X = ℓ∞`,
`u = σ − d − g` satisfies 15.1, 15.2 (it is concave), 15.3, 15.6 and 15.7, but `lim_T u(1ᵀ)` does
not exist. (In particular the "only if" of the exercise fails for this `u` too.) -/
theorem ex_15_11b_manual_counterexample :
    Convex ℝ (univ : Set (BddSeq ℝ)) ∧ SeqTruncClosed (univ : Set (BddSeq ℝ)) ∧
    SeqSemistrictQC univ oscillatingUtility ∧ ContinuousOn oscillatingUtility univ ∧
    SeqTailInsensitive univ oscillatingUtility ∧
    ¬ ∀ x ∈ (univ : Set (BddSeq ℝ)), ∃ L, Tendsto (fun T => oscillatingUtility (seqTrunc T x)) atTop
      (𝓝 L) ∧ oscillatingUtility x ≤ L := by
  have htr : ∀ x T, oscillatingUtility (seqTrunc T x) =
      halfSum (seqTrunc T x) - oddDrop (seqTrunc T x) := fun x T => by
    simp [oscillatingUtility, tailDist_of_mem (seqTrunc_mem_seqC00 T x)]
  refine ⟨convex_univ, fun _ _ => Eventually.of_forall fun _ => mem_univ _,
    SeqSemistrictQC.of_concave fun x _ x' _ θ h0 h1 =>
      concave_halfSum_sub oddDrop_convex x x' h0.le h1.le,
    ((halfSum.continuous.sub continuous_tailDist).sub continuous_oddDrop).continuousOn,
    SeqTailInsensitive.of_liminf fun x _ c hc => ?_, fun h => ?_⟩
  · set ε := (oscillatingUtility x - c) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    have h1 := (tendsto_halfSum_seqTrunc x).eventually
      (lt_mem_nhds (sub_lt_self (halfSum x) hεpos))
    filter_upwards [h1, eventually_norm_lt_tailDist_add x hεpos] with T hT1 hT2
    rw [htr]
    have := oddDrop_seqTrunc_le x T
    unfold oscillatingUtility at hε
    linarith
  · obtain ⟨L, hL, -⟩ := h oneSeq (mem_univ _)
    simp only [htr] at hL
    have hg : Tendsto (fun T => oddDrop (seqTrunc T oneSeq)) atTop (𝓝 (halfSum oneSeq - L)) :=
      ((tendsto_halfSum_seqTrunc oneSeq).sub hL).congr fun T => by ring
    have hev : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
    have hodd : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩
    have e0 := tendsto_nhds_unique (hg.comp hev)
      (tendsto_const_nhds.congr fun k => (oddDrop_seqTrunc_one k).1.symm)
    have e1 := tendsto_nhds_unique (hg.comp hodd)
      (tendsto_const_nhds.congr fun k => (oddDrop_seqTrunc_one k).2.symm)
    linarith

end StokeyLucasPrescott.ParetoOptimaEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Figure 15.3 and the p. 458 overstatement

SLP §15.2–15.3, pp. 457–458.

**Figure 15.3** (pp. 457–458) is drawn, not specified. `fig153X`, `fig153U`, `fig153Y` give a
concrete two-consumer, two-good exchange economy in `ℝ²` with the same features (the endowment
`ω = (1, 0)` is modelled as a single firm with `Y = {ω}`):
* consumer `0` has the half-plane `X₀ = {v : v₁ ≥ 0}` and `u₀(v) = v₂`;
* consumer `1` has `X₁ = ℝ²` and the smooth, strictly concave in good 2, `u₁(v) = v₁ − v₂²`;
* the allocation `E`: `x₀ = (0, 0)`, `x₁ = (1, 0)`.

Results:
* `fig153_assumptions`: Assumptions 15.1–15.5 and local nonsatiation hold.
* `fig153_paretoOptimal`: `E` is Pareto optimal.
* `fig153_supported`: `φ(v) = v₁` is a nonzero supporting price (Theorem 15.4's conclusion) at
  which consumer `0` has no cheaper point, so the Remark does not apply; and consumer `0`
  strictly prefers `E′ = (0, 1)` on her budget line.
* `fig153_not_competitiveEq`: no price system whatever makes `E` a competitive equilibrium.

**Correction** (p. 458). The book says that under Assumptions 15.1–15.5 "the set of competitive
equilibrium allocations and the set of Pareto-optimal allocations coincide exactly". Both
inclusions fail:
* `paretoOptimal_not_ce_counterexample`: the Figure 15.3 economy above satisfies 15.1–15.5 (and
  local nonsatiation) and has a Pareto optimum that is not a competitive equilibrium allocation
  (PO ⇒ CE needs the cheaper-point condition of the Remark);
* `ce_not_paretoOptimal_counterexample`: two consumers with `u(v) = min(v, 0)` on `ℝ` and endowment
  `0`; Assumptions 15.1–15.5 hold, `x = (1, −1)` with `φ = id` is a competitive equilibrium, and it
  is not Pareto optimal (CE ⇒ PO needs local nonsatiation, which fails at the satiated consumer).
The correct statement is `welfare_theorems_corrected` (`WelfareSecond`).
-/

namespace StokeyLucasPrescott.ParetoOptimaEquilibria

open Filter Topology Set

/-- If there is one firm whose production set is a single point `ω` (an endowment), the aggregate
technology is `{ω}`. -/
theorem aggTech_singleton {S : Type*} [NormedAddCommGroup S] (e : S) :
    aggTech (fun _ : Unit => ({e} : Set S)) = {e} := by
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy ()
  · rintro rfl
    exact ⟨fun _ => w, fun _ => rfl, by simp⟩

/-! ### The Figure 15.3 economy -/

/-- Consumption sets of the Figure 15.3 economy: `X₀ = {v : v₁ ≥ 0}`, `X₁ = ℝ²`. -/
def fig153X : Fin 2 → Set (ℝ × ℝ) := ![{v | 0 ≤ v.1}, univ]

/-- Utilities of the Figure 15.3 economy: `u₀(v) = v₂`, `u₁(v) = v₁ − v₂²`. -/
def fig153U : Fin 2 → ℝ × ℝ → ℝ := ![fun v => v.2, fun v => v.1 - v.2 ^ 2]

/-- The single "firm" of the Figure 15.3 economy is the endowment `ω = (1, 0)`. -/
def fig153Y : Unit → Set (ℝ × ℝ) := fun _ => {(1, 0)}

/-- The allocation `E` of the Figure 15.3 economy: `x₀ = (0, 0)`, `x₁ = (1, 0)`. -/
def fig153x : Fin 2 → ℝ × ℝ := ![(0, 0), (1, 0)]

/-- The endowment `y = ω = (1, 0)` of the Figure 15.3 economy. -/
def fig153y : Unit → ℝ × ℝ := fun _ => (1, 0)

/-- The supporting price of the Figure 15.3 economy: `φ(v) = v₁` (good 2 is free). -/
noncomputable def fig153φ : StrongDual ℝ (ℝ × ℝ) := ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The Figure 15.3 economy satisfies Assumptions 15.1–15.5 and local nonsatiation. -/
theorem fig153_assumptions :
    Assumption15_1 fig153X ∧ Assumption15_2 fig153X fig153U ∧ Assumption15_3 fig153X fig153U ∧
    Assumption15_4 fig153Y ∧ Assumption15_5 (ℝ × ℝ) fig153Y ∧
    LocalNonsatiation fig153X fig153U := by
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨?_, ?_, ?_, ?_, Or.inr inferInstance, ?_⟩
  · rw [Assumption15_1, Fin.forall_fin_two]
    refine ⟨?_, convex_univ⟩
    intro v hv w hw a b ha hb _
    simp only [fig153X, Matrix.cons_val_zero, mem_ofPred_eq, Prod.fst_add, Prod.smul_fst,
      smul_eq_mul] at hv hw ⊢
    positivity
  · rw [Assumption15_2, Fin.forall_fin_two]
    constructor
    · intro z _ z' _ hlt θ hθ0 hθ1
      simp only [fig153U, Matrix.cons_val_zero, Prod.snd_add, Prod.smul_snd,
        smul_eq_mul] at hlt ⊢
      nlinarith
    · intro z _ z' _ hlt θ hθ0 hθ1
      simp only [fig153U, Matrix.cons_val_one, Matrix.cons_val_zero, Prod.fst_add,
        Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hlt ⊢
      nlinarith [mul_nonneg (mul_nonneg hθ0.le (sub_nonneg.2 hθ1.le))
        (sq_nonneg (z.2 - z'.2))]
  · rw [Assumption15_3, Fin.forall_fin_two]
    exact ⟨by simp only [fig153U, Matrix.cons_val_zero]; exact continuous_snd.continuousOn,
      by simp only [fig153U, Matrix.cons_val_one, Matrix.cons_val_zero]
         exact (continuous_fst.sub (continuous_snd.pow 2)).continuousOn⟩
  · change Convex ℝ (aggTech (fun _ : Unit => ({((1 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ))))
    rw [aggTech_singleton]
    exact convex_singleton _
  · rw [LocalNonsatiation, Fin.forall_fin_two]
    constructor
    · intro z hz
      refine ⟨fun n => z + (0, 1 / ((n : ℝ) + 1)), fun n => ?_, ?_, fun n => ?_⟩
      · simpa [fig153X] using hz
      · have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z)).add
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).prodMk_nhds hlim)
        simpa [Prod.mk_zero_zero] using this
      · simp only [fig153U, Matrix.cons_val_zero, Prod.snd_add]
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    · intro z _
      refine ⟨fun n => z + (1 / ((n : ℝ) + 1), 0), fun n => by simp [fig153X], ?_,
        fun n => ?_⟩
      · have := (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z)).add
          (hlim.prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
        simpa [Prod.mk_zero_zero] using this
      · simp only [fig153U, Matrix.cons_val_one, Matrix.cons_val_zero, Prod.fst_add,
          Prod.snd_add, add_zero]
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith

/-- The allocation `E` of the Figure 15.3 economy is Pareto optimal. -/
theorem fig153_paretoOptimal : ParetoOptimal fig153X fig153U fig153Y fig153x fig153y := by
  refine ⟨⟨?_, fun _ => rfl, ?_⟩, ?_⟩
  · rw [Fin.forall_fin_two]
    exact ⟨by simp [fig153X, fig153x], by simp [fig153X]⟩
  · simp [fig153x, fig153y, Fin.sum_univ_two]
  · rintro ⟨x', y', ⟨hx', hy', hsum⟩, hge, i, hi⟩
    have hy0 : y' () = (1, 0) := hy' ()
    have h0 : 0 ≤ (x' 0).1 := hx' 0
    simp only [Fin.sum_univ_two, Finset.univ_unique, PUnit.default_eq_unit,
      Finset.sum_singleton, hy0] at hsum
    have e1 := congrArg Prod.fst hsum
    have e2 := congrArg Prod.snd hsum
    simp only [Prod.fst_sub, Prod.fst_add, Prod.snd_sub, Prod.snd_add, Prod.fst_zero,
      Prod.snd_zero] at e1 e2
    have g0 := hge 0
    have g1 := hge 1
    simp only [fig153U, fig153x, Matrix.cons_val_zero, Matrix.cons_val_one] at g0 g1
    have hb : (x' 1).2 = -(x' 0).2 := by linarith
    have ha : (x' 1).1 = 1 - (x' 0).1 := by linarith
    rw [hb, ha] at g1
    have hzero : (x' 0).2 = 0 := by nlinarith [sq_nonneg (x' 0).2]
    fin_cases i
    · simp only [fig153U, fig153x, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hi
      linarith
    · simp only [fig153U, fig153x, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero] at hi
      rw [hb, ha] at hi
      nlinarith [sq_nonneg (x' 0).2]

/-- At `E`, `φ(v) = v₁` is a nonzero supporting price ((3) and (4) hold), consumer `0` has no
cheaper point at `φ`, and consumer `0` strictly prefers `E′ = (0, 1)`, which costs the same. -/
theorem fig153_supported :
    fig153φ ≠ 0 ∧ SupportsAllocation fig153X fig153U fig153Y fig153x fig153y fig153φ ∧
    (∀ z ∈ fig153X 0, fig153φ (fig153x 0) ≤ fig153φ z) ∧
    ((0, 1) : ℝ × ℝ) ∈ fig153X 0 ∧ fig153φ (0, 1) ≤ fig153φ (fig153x 0) ∧
    fig153U 0 (fig153x 0) < fig153U 0 (0, 1) := by
  have hφ : ∀ v : ℝ × ℝ, fig153φ v = v.1 := fun v => rfl
  refine ⟨fun h => by simpa [hφ] using congrArg (fun f => f ((1, 0) : ℝ × ℝ)) h,
    ⟨?_, ?_⟩, ?_, by simp [fig153X], by simp [hφ, fig153x], by simp [fig153U, fig153x]⟩
  · rw [Fin.forall_fin_two]
    constructor
    · intro z hz _
      simpa [hφ, fig153x, fig153X] using hz
    · intro z _ hle
      simp only [fig153U, fig153x, Matrix.cons_val_one, Matrix.cons_val_zero] at hle
      simp only [hφ, fig153x, Matrix.cons_val_one, Matrix.cons_val_zero]
      nlinarith [sq_nonneg z.2]
  · intro j w hw
    rw [show w = (1, 0) from hw]
    exact le_rfl
  · intro z hz
    simpa [hφ, fig153x, fig153X] using hz

/-- **No price system supports `E` as a competitive equilibrium** (Figure 15.3). If `φ` were an
equilibrium price, consumer `0`'s optimality would force `φ(0, 1) > 0`, and then consumer `1` could
afford a strictly better bundle. -/
theorem fig153_not_competitiveEq :
    ¬ ∃ φ, CompetitiveEq fig153X fig153U fig153Y fig153x fig153y φ := by
  rintro ⟨φ, -, hE2, -⟩
  set p1 := φ (1, 0) with hp1
  set p2 := φ (0, 1) with hp2
  have hφ : ∀ a b : ℝ, φ (a, b) = a * p1 + b * p2 := by
    intro a b
    have : ((a, b) : ℝ × ℝ) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  -- consumer `0`: the bundle `(0, 1)` must be unaffordable, so `p2 > 0`
  have hp2pos : 0 < p2 := by
    by_contra hle
    push Not at hle
    have := hE2 0 (0, 1) (by simp [fig153X]) (by simp [fig153x, hφ, hle])
    norm_num [fig153U, fig153x] at this
  -- consumer `1`
  have h1 := fun z => hE2 1 z (by simp [fig153X])
  simp only [fig153U, fig153x, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
  rcases le_or_gt p1 0 with hp1n | hp1p
  · have := h1 (2, 0) (by rw [hφ, hφ]; nlinarith)
    norm_num at this
  · set a := p2 / (2 * p1) with ha
    have hapos : 0 < a := div_pos hp2pos (by linarith)
    have hrel : 2 * p1 * a = p2 := by
      rw [ha]
      field_simp
    have := h1 (1 + 2 * a ^ 2, -a) (by rw [hφ, hφ]; nlinarith)
    nlinarith

/-- **Counterexample** to the p. 458 claim "PO ⇒ CE under Assumptions 15.1–15.5": the Figure 15.3
economy satisfies Assumptions 15.1–15.5 and local nonsatiation, but its Pareto optimum `E` is not
a competitive equilibrium allocation for any price system. -/
theorem paretoOptimal_not_ce_counterexample :
    Assumption15_1 fig153X ∧ Assumption15_2 fig153X fig153U ∧ Assumption15_3 fig153X fig153U ∧
    Assumption15_4 fig153Y ∧ Assumption15_5 (ℝ × ℝ) fig153Y ∧
    LocalNonsatiation fig153X fig153U ∧
    ¬ ∀ x y, ParetoOptimal fig153X fig153U fig153Y x y →
      ∃ φ, CompetitiveEq fig153X fig153U fig153Y x y φ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := fig153_assumptions
  exact ⟨h1, h2, h3, h4, h5, h6, fun h =>
    fig153_not_competitiveEq (h fig153x fig153y fig153_paretoOptimal)⟩

/-! ### A competitive equilibrium that is not Pareto optimal -/

/-- Utilities of the satiation example: both consumers have `u(v) = min(v, 0)` on `ℝ`. -/
noncomputable def satU : Fin 2 → ℝ → ℝ := fun _ v => min v 0

/-- **Counterexample** to the p. 458 claim "CE ⇒ PO under Assumptions 15.1–15.5". Two consumers
with `X = ℝ`, `u(v) = min(v, 0)`, endowment `0` (one firm, `Y = {0}`). Assumptions 15.1–15.5 hold;
the allocation `x = (1, −1)` with the price `φ = id` is a competitive equilibrium, but it is not
Pareto optimal (`(0, 0)` makes consumer `1` better off and consumer `0` no worse off); local
nonsatiation fails at consumer `0`'s satiated bundle `1`. -/
theorem ce_not_paretoOptimal_counterexample :
    Assumption15_1 (fun _ : Fin 2 => (univ : Set ℝ)) ∧
    Assumption15_2 (fun _ : Fin 2 => (univ : Set ℝ)) satU ∧
    Assumption15_3 (fun _ : Fin 2 => (univ : Set ℝ)) satU ∧
    Assumption15_4 (fun _ : Unit => ({0} : Set ℝ)) ∧
    Assumption15_5 ℝ (fun _ : Unit => ({0} : Set ℝ)) ∧
    CompetitiveEq (fun _ : Fin 2 => (univ : Set ℝ)) satU (fun _ : Unit => ({0} : Set ℝ))
      ![1, -1] (fun _ => 0) (ContinuousLinearMap.id ℝ ℝ) ∧
    ¬ ParetoOptimal (fun _ : Fin 2 => (univ : Set ℝ)) satU (fun _ : Unit => ({0} : Set ℝ))
      ![1, -1] (fun _ => 0) ∧
    ¬ LocalNonsatiation (fun _ : Fin 2 => (univ : Set ℝ)) satU := by
  refine ⟨fun _ => convex_univ, ?_, fun _ => (continuous_id.min continuous_const).continuousOn,
    by rw [Assumption15_4, aggTech_singleton]; exact convex_singleton _, Or.inr inferInstance,
    ⟨⟨fun _ => mem_univ _, fun _ => rfl, by simp [Fin.sum_univ_two]⟩,
      fun i z _ hz => min_le_min_right 0 hz, fun j w hw => by rw [show w = 0 from hw]⟩,
    ?_, ?_⟩
  · intro i z _ z' _ hlt θ hθ0 hθ1
    simp only [satU, smul_eq_mul] at hlt ⊢
    have hz' : z' < 0 := by
      by_contra hge
      push Not at hge
      rw [min_eq_right hge] at hlt
      linarith [min_le_right z 0]
    have hzz : z' < z := by
      by_contra hge
      push Not at hge
      linarith [min_le_min_right 0 hge]
    rw [min_eq_left hz'.le]
    exact lt_min (by nlinarith) hz'
  · rintro ⟨-, hno⟩
    refine hno ⟨![0, 0], fun _ => 0, ⟨fun _ => mem_univ _, fun _ => rfl, by simp⟩, ?_, 1, ?_⟩
    · rw [Fin.forall_fin_two]
      norm_num [satU]
    · norm_num [satU]
  · intro hLNS
    obtain ⟨zs, -, -, hzs⟩ := hLNS 0 1 (mem_univ _)
    have := hzs 0
    simp only [satU] at this
    linarith [min_le_right (zs 0) 0, show min (1 : ℝ) 0 = 0 from min_eq_right zero_le_one]

end StokeyLucasPrescott.ParetoOptimaEquilibria

set_option linter.style.longLine false
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Feasible
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ParetoOptimal
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.CompetitiveEq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.LocalNonsatiation
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.aggTech
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_1
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_2
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_3
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_4
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_5
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ce_cost_le_of_utility_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ce_cost_lt_of_utility_lt
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_3
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.quasiconcave_real_of_semistrict
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.quasiconcave_of_assumptions
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.convex_weaklyPreferred
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.convex_strictlyPreferred
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.convexCounterU
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.assumption15_2_convex_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.closureCounterU
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.continuity_closure_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.weaklyPreferred_subset_closure
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_dual_nonneg_of_zero_notMem
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_separating_of_finiteDimensional
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_separating_of_interior
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_separating_of_assumption15_5
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.SupportsAllocation
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.preferredSum
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.convex_preferredSum
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.preferredSum_nonempty
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.preferredSum_disjoint
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.le_of_weaklyPreferred
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_4
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.remark_cheaper_point
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_better_of_localNonsatiation
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.welfare_theorems_corrected
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.aggTech_of_unit
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.lpPosOrthant
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_7a
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_7b
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158X
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158Y
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158U
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.bddBelow_range_lpInfty
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158U_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.le_ex158U
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158U_le_one
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.abs_ex158U_sub_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.half_mem_interior_ex158Y
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_8
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158x0
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158x0_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158U_x0
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158_paretoOptimal
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158_nonsatiated
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158_exists_price
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158e
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158e_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158x0_sub_single_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158_price_vanishes_single
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex158_no_inner_product
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.weightedDist
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.weightedDist_update
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.summable_weighted_update
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_9
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.weighted_orthant_no_interior
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.weighted_no_interior_of_subset_orthant
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.hasSum_state_probabilities
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.SeqContAt
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_1a
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.continuous_iff_seqContAt
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_1b
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dual_norm_eq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_1
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.intro_concavity_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.example_15_1
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ellInfSp
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ellOneSp
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ellTwoSp
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairInfOne
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairOneInf
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairTwo
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairInfOne_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairOneInf_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairTwo_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_pairInfOne_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_pairOneInf_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_single_one
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tsum_mul_single
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_ellOneSp_eq_tsum
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.summable_abs_ellOneSp
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.summable_mul_of_one_inf
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_3
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_3_manual_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_pairInfOne
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairInfOne_surjective
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualEllOne
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_2b
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairTwo_eq_toDual
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_pairTwo
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairTwo_surjective
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualEllTwo
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_2a
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairEllP
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairEllP_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_pairEllP_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.sum_rpow_le_of_dual_ellP
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_preimage_pairEllP
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_pairEllP
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualEllP
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.example_15_2
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.cZero
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.mem_cZero
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.isClosed_cZero
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_4a
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.signTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.signTrunc_mem
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_signTrunc_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tsum_mul_signTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairOneCZero
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairOneCZero_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_pairOneCZero
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.unitCZero
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tendsto_trunc_cZero
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairOneCZero_surjective
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualCZero
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_4b
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairL1Linf
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairLinfL1
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairL1Linf_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairLinfL1_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.abs_pairL1Linf_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.abs_pairLinfL1_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_5a
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_5b
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.indicatorConstLp_one_eq_smul
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairLinfL1_indicator
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairLinfL1_injective
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_preimage_pairLinfL1
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_pairLinfL1
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualL1
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.l1_dual_sigmaFinite
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.infAtom
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.subsingleton_L1_infAtom
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.nontrivial_Linf_infAtom
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.l1_dual_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.l1_dual_pairing_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.positive_measure_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.of_ae_of_atoms_pos
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ae_norm_le_norm_Linf
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.memLp_ellInfSp
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ellInfToLinf
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.coeFn_ellInfToLinf
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_ellInfToLinf
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ellInfToLinf_surjective
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.example_15_4_linf_nat
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_const_between_of_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_2_interior
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_2_finiteDimensional
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_2
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.BookTheorem15_2
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_lt_apply_of_ne_zero
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_2_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_2_counterexample_finiteDimensional
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_6
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.weightToEllOne
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dist_weightToEllOne
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.weightToEllOne_surjective
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex156Box
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.weightToEllOne_mem_ex156Box_iff
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.convex_ex156Box
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.zero_mem_ex156Box
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.interior_ex156Box
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_6_zero_notMem_interior
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.eq_zero_of_le_zero_on_ex156Box
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_6_no_separation
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.indicatorConstLp_biUnion
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.hasSum_indicatorConstLp
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualSignedMeasure
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualSignedMeasure_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.indicatorConstLp_eq_zero_of_null
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualSignedMeasure_ac
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualDensity
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.integrable_dualDensity
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.setIntegral_dualDensity
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.indicatorConstLp_eq_smul
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualDensity_simpleFunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.signedApprox
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.eapprox_le_self
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tendsto_eapprox_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.signedApprox_bounds
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tendsto_signedApprox
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.le_rpow_of_le_mul_rpow
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.eLpNorm_dualDensity_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairLqLp
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairLqLp_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.abs_pairLqLp_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairLqLp_indicator
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairLqLp_injective
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_preimage_pairLqLp
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_pairLqLp
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualLp
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.example_15_4
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ae_eq_rpow_mul_of_withDensity
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.eLpNorm_rpow_mul
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.rpow_mul_rpow_neg_mul
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.memLp_rpow_mul
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.memLp_rpow_neg_mul
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsDualRep
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.isDualRep_of_weight
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.testFn
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.mul_testFn
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.abs_testFn
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.measurable_testFn
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.memLp_testFn
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_toLp_testFn
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsDualRep.integral_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsDualRep.eLpNorm_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_pairLqLp_eq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.pairLqLp_injective_of_ne_top
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_preimage_pairLqLp_sigmaFinite
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualLpSigmaFinite
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.example_15_4_sigmaFinite
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsDualRep.ae_eq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsDualRep.indicator
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.sigmaFinite_restrict_iUnion
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_isDualRep
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_sigmaFinite_support
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_preimage_pairLqLp_of_ne_top
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.dualLpOfNeTop
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.example_15_4_general
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ae_abs_le_norm_linfty
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_linfty_le_of_ae_abs_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrictFn
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.coeFn_linftyRestrictFn
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrictLM
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_linftyRestrictFn_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrict
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrict_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrict_of_not_measurable
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.coeFn_linftyRestrict
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_linftyRestrict_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.opNorm_linftyRestrict_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrict_linftyRestrict
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrict_union
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrict_univ
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrict_of_null
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_linftyRestrict_add_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrictNorm
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrictNorm_nonneg
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrictNorm_le_norm
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.abs_apply_linftyRestrict_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrictNorm_mono
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linfty_exists_apply_eq_abs
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrictNorm_add_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTailInf
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTailInf_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTailInf_nonneg
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTailInf_le_norm
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTailInf_mono
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTailSup
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.bddAbove_linftyTailInf
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTailInf_le_linftyTailSup
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tendsto_linftyTailInf
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.mk
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.measurableSet
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.antitone
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.measure_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.linftyRestrictNorm_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_isLinftyTailSeq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.tailInf_le_restrictNorm
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTrunc_sub_linftyTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.abs_sub_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.cauchySeq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTruncLimit
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.tendsto
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.limitDual
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.limitDual_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.norm_limitDual_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.abs_linftyTruncLimit_restrict_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.linftyTruncLimit_linftyTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.tendsto_linftyTruncLimit_restrict
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyOne
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.coeFn_linftyOne
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_linftyOne_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.coeFn_linftyRestrict_one
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrictNorm_sum_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyRestrict_sum
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.limitSignedMeasure
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.limitSignedMeasure_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsLinftyTailSeq.limitSignedMeasure_absolutelyContinuous
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyL1Pairing
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyL1Pairing_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linfty_dual_eq_zero
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.lemma_15_7
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.LinftyNullSeq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.LinftyNullSeq.mk
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.LinftyNullSeq.measurableSet
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.LinftyNullSeq.antitone
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.LinftyNullSeq.tendsto_measure
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_8
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_9
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.supportsAllocation_of_limit_bounds
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_8
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_8_inner_product
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyExpectedUtility
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ae_abs_le_norm_linfty_of_ac
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_abs_le_of_continuous
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.integrable_comp_linfty
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_12_continuous
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_12_tendsto
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_12_assumption15_9
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_12_assumption15_3
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_12_concave
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_12_assumption15_2
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_12
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.finTwoUniform
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.isProbabilityMeasure_finTwoUniform
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ae_finTwoUniform_iff
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.finTwoUniform_expectedUtility
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.memLp_finTwoUniform
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.finTwoVec
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.finTwoVec_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_12_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.LinftyTimeState
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_linftyTimeState_apply_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_coord_le_of_opNorm_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyCoordMap
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyCoordMap_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_linftyCoordMap_apply_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTimeTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTimeTrunc_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyEventTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyEventTrunc_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyPeriodTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyPeriodTrunc_apply_self
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyPeriodTrunc_apply_of_ne
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTSSingle
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTSSingle_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTSSingle_sum_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyCoordDual
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyCoordDual_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.sum_abs_linftyCoordDual_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.summable_abs_of_sum_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftySumDual
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.hasSum_linftySumDual
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_linftySumDual_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_linftyTimeState_decomposition
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_6_timeState
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_7_timeState
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_8'
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_9'
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyPeriodTrunc_drop
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTimeTrunc_drop
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTS_consumer_bound
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.linftyTS_firm_bound
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_9
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.BddSeq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_seq_coord_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.BddSeq.mk
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.BddSeq.mk_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seq_sum_single_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqTruncFun
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_seqTruncFun_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqTrunc_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_seqTrunc_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqTrunc_eq_sum_single
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqTrunc_seqTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqC00
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqTrunc_mem_seqC00
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.eventually_seqTrunc_eq_of_mem_seqC00
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.coordFunctional
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.coordFunctional_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.apply_seqTrunc_eq_sum
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.sum_abs_coordFunctional_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.summable_abs_coordFunctional
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.summable_coordFunctional
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tsum_abs_coordFunctional_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqRegularPartLinear
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.abs_seqRegularPartLinear_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqRegularPart
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqRegularPart_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.hasSum_seqRegularPart
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tendsto_apply_seqTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_seqRegularPart_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqRegularPart_eq_of_mem_seqC00
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqRegularPart_seqTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqRegularPart_seqRegularPart
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.lemma_15_5
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.oneSeq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_oneSeq_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqRegularPart_real
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqRegularPart_euclid
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.SeqSemistrictQC
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.assumption15_2_iff_seq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.SeqSemistrictQC.of_concave
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.SeqTruncClosed
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.SeqTailInsensitive
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_6
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.Assumption15_7
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.SeqTailInsensitive.eventually
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.SeqTailInsensitive.of_liminf
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.SeqTailInsensitive.of_tendsto
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqSet
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seq_coord_combo
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.convex_seqSet
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqTrunc_mem_seqSet
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_10a
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.discountedUtility
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_discounted_term_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.summable_discounted
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tendsto_discountedUtility_seqTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_10b_tail
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.continuous_seq_coord
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_10b_continuousOn
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.discountedUtility_concave
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_10b
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.discountedUtility_half_values
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_10b_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqShift
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqShift_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqShift_seqTrunc_succ
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqShift_mem_seqSet
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregator
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregator.mk
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregator.beta_pos
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregator.beta_lt_one
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregator.continuousOn
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregator.zero
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregator.bounded
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregator.nonneg
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregator.lipschitz
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregatorFixedPoint
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregatorFixedPoint.mk
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregatorFixedPoint.bounded
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregatorFixedPoint.continuousOn
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregatorFixedPoint.nonneg
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.IsAggregatorFixedPoint.fixed
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.aggregator_seqTrunc_bound
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_10c_tail
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seq_monotoneOn_of_concave_nonneg
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.aggregator_monotone
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.aggregator_concave_approx
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_10c
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_10c_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.summable_half_mul
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.halfSumLinear
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_halfSumLinear_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.halfSum
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.halfSum_apply
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.hasSum_halfSum
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.halfSum_single
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tendsto_halfSum_seqTrunc
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tailDist
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqC00_nonempty
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tailDist_nonneg
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tailDist_of_mem
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.continuous_tailDist
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tailDist_convex
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.eventually_norm_lt_tailDist_add
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tailDist_oneSeq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.norm_quotient_seqC00_mk
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.exists_seq_functional_at_infinity
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seq_apply_nonpos_of_nonpos
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqRegularPart_eq_zero_of_seqC00
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seq_tendsto_segment
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seq_support_step1_consumer
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seq_support_step1_firm
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seq_support_step2
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_6
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_6_of_supporting
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seq_budget_max_of_cheaper
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_6_competitiveEq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.seqRegularPart_ne_zero_of_cheaper
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.halfSum_nonpos
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.theorem_15_6_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.infUtility
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_11a
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_11b_if
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_11b_liminf
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.tailPenalizedUtility
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.concave_halfSum_sub
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_11b_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.oddDrop
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.oddDrop_term_le_norm
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.oddDrop_bddAbove
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.oddDrop_term_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.oddDrop_nonneg
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.oddDrop_convex
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.continuous_oddDrop
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.oddDrop_seqTrunc_le
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.oddDrop_seqTrunc_one
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.oscillatingUtility
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ex_15_11b_manual_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.aggTech_singleton
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.fig153X
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.fig153U
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.fig153Y
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.fig153x
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.fig153y
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.fig153φ
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.fig153_assumptions
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.fig153_paretoOptimal
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.fig153_supported
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.fig153_not_competitiveEq
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.paretoOptimal_not_ce_counterexample
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.satU
#print axioms StokeyLucasPrescott.ParetoOptimaEquilibria.ce_not_paretoOptimal_counterexample
