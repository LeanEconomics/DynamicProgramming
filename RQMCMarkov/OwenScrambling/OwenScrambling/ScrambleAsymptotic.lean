/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.ScrambleVariance
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Scrambled nets are asymptotically better than Monte Carlo: `Var = o(1/n)` (Owen 1997)

Owen (1997): for every `f ∈ L²`, the scrambled `(0,m,s)`-net variance is `o(1/n)`. The proof here
avoids the infinite Haar expansion: the estimator is EXACT for step functions on elementary cubes
of level `R` with `sR ≤ m` (the scrambled net puts `b^{m-sR}` points in each), so it has the same
variance for `f` and `f - g` (`g` such a step function); by Owen's bound this is at most
`C ‖f - g‖²/n`, and step functions are dense in `L²` (`exists_stepFn_approx`).

## Main results

* `card_box_net_of_le`: a `(0,m,s)`-net puts exactly `b^{m-|r|}` points in every box with
  `|r| ≤ m`.
* `stepFn`, `sum_stepFn_scrambledPoint`, `integral_stepFn`, `sampleMean_stepFn_scrambledPoint`:
  scrambled nets integrate level-`R` step functions exactly when `sR ≤ m`, for every scramble.
* `variance_scrambledLaw_eq_sum`, `variance_scrambledLaw_sub_of_exact`: subtracting an exactly
  integrated function leaves the variance unchanged.
* `dist_corner_lt`, `exists_stepFn_approx`: bounded step functions approximate any `f ∈ L²` in
  mean square at every fine enough level (via a bounded continuous approximant, Mathlib's
  `MemLp.exists_boundedContinuous_integral_rpow_sub_le`, and Heine–Cantor on `[0,1]^s`).
* `tendsto_pow_mul_variance_scrambledLaw` (**Owen 1997, `Var = o(1/n)`**): for `(0,m,s)`-nets
  (`1 ≤ s ≤ b + 1`, `m` digits) and every measurable `f ∈ L²`, `n Var(μ̂) → 0`.
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal Topology

variable {b D : ℕ}

/-- **Box counts of a `(0,m,s)`-net** (`m ≤ D`): every elementary box of levels `r` with
`|r| ≤ m` contains exactly `b^{m - |r|}` points. -/
theorem card_box_net_of_le (hb : 0 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {r : Fin s → ℕ}
    (hr : ∑ j, r j ≤ m) {a : Fin s → ℕ} (ha : ∀ j, a j < b ^ r j) :
    (Finset.univ.filter fun i' ↦ ∀ j, prefixVal (d i' j) (r j) = a j).card =
      b ^ (m - ∑ j, r j) := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have : (Finset.univ.filter fun i' : Fin n ↦ ∀ j : Fin 0, prefixVal (d i' j) (r j) = a j) =
        Finset.univ := Finset.filter_true_of_mem fun i' _ j ↦ j.elim0
    rw [this, Finset.card_univ, Fintype.card_fin, hnet.2.1, Finset.univ_eq_empty,
      Finset.sum_empty, Nat.sub_zero]
  set j₀ : Fin s := ⟨0, hs⟩
  set e := m - ∑ j, r j with he
  set r' : Fin s → ℕ := Function.update r j₀ (r j₀ + e) with hr'
  have hsplit : ∀ g : Fin s → ℕ, ∑ j, g j = g j₀ + ∑ j ∈ Finset.univ \ {j₀}, g j := fun g ↦ by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), Finset.sdiff_singleton_eq_erase]
  have hr'sum : ∑ j, r' j = m := by
    rw [hsplit r', hr', Function.update_self]
    have : ∑ j ∈ Finset.univ \ {j₀}, Function.update r j₀ (r j₀ + e) j =
        ∑ j ∈ Finset.univ \ {j₀}, r j := Finset.sum_congr rfl fun j hj ↦
      Function.update_of_ne (Finset.notMem_singleton.1 (Finset.mem_sdiff.1 hj).2) _ _
    rw [this]
    have := hsplit r
    omega
  have hr'D : ∀ j, r' j ≤ D := fun j ↦ le_trans (le_trans
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (r' j)) (Finset.mem_univ j)) hr'sum.le) hmD
  set S := Finset.univ.filter fun i' ↦ ∀ j, prefixVal (d i' j) (r j) = a j with hS
  set f : Fin n → ℕ := fun i' ↦ prefixVal (d i' j₀) (r j₀ + e) with hf
  set T := (Finset.range (b ^ r j₀ * b ^ e)).filter fun A ↦ A / b ^ e = a j₀ with hT
  have hdiv : ∀ i' : Fin n, prefixVal (d i' j₀) (r j₀ + e) / b ^ e = prefixVal (d i' j₀) (r j₀) :=
    fun i' ↦ by
      have := prefixVal_div hb (d i' j₀) (Nat.le_add_right (r j₀) e)
      rwa [Nat.add_sub_cancel_left] at this
  have hmaps : (S : Set (Fin n)).MapsTo f T := by
    intro i' hi'
    rw [Finset.mem_coe, hS, Finset.mem_filter] at hi'
    rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_range, ← pow_add, hf]
    refine ⟨prefixVal_lt hb _ _, ?_⟩
    rw [hdiv i']
    exact hi'.2 j₀
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ A ∈ T, (S.filter fun i' ↦ f i' = A).card = 1 := by
    intro A hA
    rw [hT, Finset.mem_filter, Finset.mem_range] at hA
    have h := hnet.2.2.2 r' (Function.update a j₀ A)
      (by rw [hr'sum, Nat.sub_zero]) (by
        intro j
        by_cases hj : j = j₀
        · subst hj
          rw [Function.update_self, hr', Function.update_self, pow_add]
          exact hA.1
        · rw [Function.update_of_ne hj, hr', Function.update_of_ne hj]
          exact ha j)
    rw [pow_zero] at h
    rw [← h, hS, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun i' _ ↦ ?_
    rw [boxIndex_digitPoint hb hr'D, funext_iff]
    constructor
    · rintro ⟨hag, hfA⟩ j
      by_cases hj : j = j₀
      · subst hj
        rw [Function.update_self, hr', Function.update_self]
        exact hfA
      · rw [Function.update_of_ne hj, hr', Function.update_of_ne hj]
        exact hag j
    · intro hall
      have h0 := hall j₀
      rw [Function.update_self, hr', Function.update_self] at h0
      refine ⟨fun j ↦ ?_, h0⟩
      by_cases hj : j = j₀
      · subst hj
        rw [← hdiv i', h0, hA.2]
      · have hj' := hall j
        rw [Function.update_of_ne hj, hr', Function.update_of_ne hj] at hj'
        exact hj'
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_one, hT,
    card_filter_range_div (Nat.pow_pos hb) (ha j₀)]

/-- A **step function on the level-`R` elementary cubes**: `x ↦ G(⌊b^R x⌋)`. -/
noncomputable def stepFn (b R : ℕ) {s : ℕ} (G : (Fin s → ℕ) → ℝ) (x : Fin s → ℝ) : ℝ :=
  G (boxIndex b (fun _ ↦ R) x)

/-- Step functions are measurable. -/
theorem measurable_stepFn (b R : ℕ) {s : ℕ} (G : (Fin s → ℕ) → ℝ) : Measurable (stepFn b R G) := by
  have h : Measurable (boxIndex b (fun _ : Fin s ↦ R)) :=
    measurable_pi_iff.2 fun j ↦ ((measurable_pi_apply j).const_mul _).nat_floor
  exact (measurable_of_countable G).comp h

/-- A step function with bounded values is in `L^p` of the cube. -/
theorem memLp_stepFn (b R : ℕ) {s : ℕ} {G : (Fin s → ℕ) → ℝ} {M : ℝ} (hG : ∀ a, |G a| ≤ M)
    (p : ℝ≥0∞) : MemLp (stepFn b R G) p (uniformCube s) := by
  have := isProbabilityMeasure_uniformCube s
  exact MemLp.of_bound (measurable_stepFn b R G).aestronglyMeasurable M
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hG _)

/-- The level-`R` box index of a scrambled point is the vector of scrambled prefix values. -/
theorem boxIndex_scrambledPoint (hb : 0 < b) {s R : ℕ} (hRD : R ≤ D) (ρ : Fin s → Scramble b D)
    (c : Fin s → Fin D → Fin b) {u : Fin s → ℝ} (hu : ∀ j, u j ∈ Set.Ico (0 : ℝ) 1) :
    boxIndex b (fun _ ↦ R) (scrambledPoint ρ c u) = fun j ↦ prefixVal (scramble (ρ j) (c j)) R :=
  funext fun j ↦ floor_pow_mul_digitPoint hb _ (hu j) hRD

/-- **Scrambled `(0,m,s)`-nets sum step functions exactly** (levels `R` with `sR ≤ m`): every
level-`R` cube holds `b^{m - sR}` scrambled points, for every scramble and remainders. -/
theorem sum_stepFn_scrambledPoint (hb : 0 < b) {m s n R : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hRD : R ≤ D) (hsR : s * R ≤ m)
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0)
    (G : (Fin s → ℕ) → ℝ) (ρ : Fin s → Scramble b D) {u : Fin n → Fin s → ℝ}
    (hu : ∀ i j, u i j ∈ Set.Ico (0 : ℝ) 1) :
    ∑ i, stepFn b R G (scrambledPoint ρ (d i) (u i)) =
      (b : ℝ) ^ (m - s * R) *
        ∑ a ∈ Fintype.piFinset fun _ : Fin s ↦ Finset.range (b ^ R), G a := by
  have hnet' : IsNet b 0 m fun i j ↦ digitPoint (scramble (ρ j) (d i j)) 0 :=
    isNet_scrambledPoint hb (by omega) hnet ρ (u := fun _ _ ↦ 0)
      (fun _ _ ↦ ⟨le_rfl, one_pos⟩)
  set key : Fin n → Fin s → ℕ := fun i j ↦ prefixVal (scramble (ρ j) (d i j)) R with hkey
  have hstep : ∀ i, stepFn b R G (scrambledPoint ρ (d i) (u i)) = G (key i) := fun i ↦ by
    unfold stepFn
    rw [boxIndex_scrambledPoint hb hRD ρ (d i) (hu i)]
  set T := Fintype.piFinset fun _ : Fin s ↦ Finset.range (b ^ R) with hT
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin n)), key i ∈ T := by
    intro i _
    rw [hT, Fintype.mem_piFinset]
    exact fun j ↦ Finset.mem_range.2 (prefixVal_lt hb _ _)
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i,
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun i ↦ G (key i)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [hT, Fintype.mem_piFinset] at ha
  have hcard : (Finset.univ.filter fun i ↦ key i = a).card = b ^ (m - s * R) := by
    have hsum : ∑ _j : Fin s, R = s * R := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have h := card_box_net_of_le hb hmD hnet' (r := fun _ ↦ R) (by rw [hsum]; exact hsR)
      (a := a) (fun j ↦ Finset.mem_range.1 (ha j))
    rw [hsum] at h
    rw [← h]
    congr 1
    exact Finset.filter_congr fun i _ ↦ funext_iff
  rw [Finset.sum_congr rfl fun i hi ↦ by rw [(Finset.mem_filter.1 hi).2], Finset.sum_const,
    hcard, nsmul_eq_mul, Nat.cast_pow]

/-- Points of `U[0,1)^s` lie in `[0,1)^s` almost surely. -/
theorem ae_mem_cube_uniformCube (s : ℕ) :
    ∀ᵐ u ∂(uniformCube s), ∀ j, u j ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro j
  have hmp : MeasurePreserving (Function.eval j) (uniformCube s) uniformIco := by
    have := isProbabilityMeasure_uniformIco
    exact measurePreserving_eval (fun _ : Fin s ↦ uniformIco) j
  have h0 : ∀ᵐ v ∂uniformIco, v ∈ Set.Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico
  rw [← hmp.map_eq] at h0
  exact ae_of_ae_map hmp.measurable.aemeasurable h0

/-- **The integral of a step function**: `∫ G(⌊b^R x⌋) dx = b^{-sR} Σ_a G(a)`. -/
theorem integral_stepFn (hb : 0 < b) {s : ℕ} (R : ℕ) {G : (Fin s → ℕ) → ℝ} {M : ℝ}
    (hG : ∀ a, |G a| ≤ M) :
    ∫ x, stepFn b R G x ∂(uniformCube s) =
      (∑ a ∈ Fintype.piFinset fun _ : Fin s ↦ Finset.range (b ^ R), G a) / ((b : ℝ) ^ R) ^ s := by
  have := isProbabilityMeasure_uniformCube s
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbR : (0 : ℝ) < ((b : ℝ) ^ R) ^ s := pow_pos (pow_pos hb' R) s
  have h := sum_integral_cellPoint (D := R) hb ((memLp_stepFn b R hG 1).integrable le_rfl)
  have hcube := ae_mem_cube_uniformCube s
  have hcell : ∀ y : Fin s → Fin R → Fin b,
      ∫ u, stepFn b R G (cellPoint y u) ∂(uniformCube s) = G fun j ↦ cellVal (y j) := by
    intro y
    rw [integral_congr_ae (g := fun _ ↦ G fun j ↦ cellVal (y j)) ?_, integral_const,
      probReal_univ, one_smul]
    filter_upwards [hcube] with u hu
    unfold stepFn
    congr 1
    funext j
    exact floor_pow_mul_digitPoint hb (y j) (hu j) le_rfl
  rw [Finset.sum_congr rfl fun y _ ↦ hcell y] at h
  have hbij : ∑ y : Fin s → Fin R → Fin b, G (fun j ↦ cellVal (y j)) =
      ∑ a ∈ Fintype.piFinset fun _ : Fin s ↦ Finset.range (b ^ R), G a := by
    refine Finset.sum_bij (fun y _ ↦ fun j ↦ cellVal (y j)) ?_ ?_ ?_ ?_
    · intro y _
      rw [Fintype.mem_piFinset]
      exact fun j ↦ Finset.mem_range.2 (cellVal_lt hb _)
    · intro y _ y' _ hyy
      funext j
      exact cellVal_injective hb (congrFun hyy j)
    · intro a ha
      rw [Fintype.mem_piFinset] at ha
      have hex : ∀ j, ∃ x : Fin R → Fin b, cellVal x = a j := fun j ↦ by
        obtain ⟨x, hx⟩ := (cellFin_bijective (D := R) hb).2 ⟨a j, Finset.mem_range.1 (ha j)⟩
        exact ⟨x, congrArg Fin.val hx⟩
      choose y hy using hex
      exact ⟨y, Finset.mem_univ _, funext hy⟩
    · intro y _
      rfl
  rw [hbij] at h
  rw [h]
  field_simp

/-- The remainders lie in the cube almost surely. -/
theorem ae_mem_cube_remLaw (s n : ℕ) :
    ∀ᵐ u ∂(remLaw s n), ∀ i j, u i j ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  have := isProbabilityMeasure_uniformIco
  have hmp : MeasurePreserving (fun u : Fin n → Fin s → ℝ ↦ u i j) (remLaw s n) uniformIco :=
    (measurePreserving_eval (fun _ : Fin s ↦ uniformIco) j).comp
      (measurePreserving_remLaw_eval s i)
  have h0 : ∀ᵐ v ∂uniformIco, v ∈ Set.Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico
  rw [← hmp.map_eq] at h0
  exact ae_of_ae_map hmp.measurable.aemeasurable h0

/-- **Exactness of the scrambled-net estimator for step functions**: for a scrambled
`(0,m,s)`-net and a bounded step function at level `R` with `sR ≤ m`, the estimator equals the
integral, for every scramble and all remainders in `[0,1)`. -/
theorem sampleMean_stepFn_scrambledPoint (hb : 0 < b) {m s R : ℕ}
    {d : Fin (b ^ m) → Fin s → Fin D → Fin b} (hmD : m ≤ D) (hRD : R ≤ D) (hsR : s * R ≤ m)
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) {G : (Fin s → ℕ) → ℝ} {M : ℝ}
    (hG : ∀ a, |G a| ≤ M) (ρ : Fin s → Scramble b D) {u : Fin (b ^ m) → Fin s → ℝ}
    (hu : ∀ i j, u i j ∈ Set.Ico (0 : ℝ) 1) :
    sampleMean (b ^ m) (stepFn b R G) (fun i ↦ scrambledPoint ρ (d i) (u i)) =
      ∫ x, stepFn b R G x ∂(uniformCube s) := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  unfold sampleMean
  rw [sum_stepFn_scrambledPoint hb hmD hRD hsR hnet G ρ hu, integral_stepFn hb R hG]
  have hpow : (b : ℝ) ^ (m - s * R) * ((b : ℝ) ^ R) ^ s = (b : ℝ) ^ m := by
    rw [← pow_mul, ← pow_add, mul_comm R s, Nat.sub_add_cancel hsR]
  have hbR : (0 : ℝ) < ((b : ℝ) ^ R) ^ s := pow_pos (pow_pos hb' R) s
  rw [Nat.cast_pow, ← hpow]
  field_simp

/-- The variance of the scrambled estimator as an average of mean squared errors. -/
theorem variance_scrambledLaw_eq_sum (hb : 0 < b) {s n : ℕ} (hn : n ≠ 0)
    {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s))
    (d : Fin n → Fin s → Fin D → Fin b) :
    Var[fun x ↦ x; scrambledLaw f d] = (Fintype.card (Fin s → Scramble b D) : ℝ)⁻¹ *
      ∑ ρ, ∫ u, (scrambledEstimate f d ρ u - ∫ x, f x ∂(uniformCube s)) ^ 2 ∂(remLaw s n) := by
  rw [variance_eq_integral (X := fun x : ℝ ↦ x) aemeasurable_id]
  change ∫ x, (x - ∫ y, y ∂(scrambledLaw f d)) ^ 2 ∂(scrambledLaw f d) = _
  rw [integral_scrambledLaw hb hn hfm hf d]
  unfold scrambledLaw
  exact integral_mixLaw (g := fun x ↦ (x - ∫ x, f x ∂(uniformCube s)) ^ 2)
    (measurable_scrambledEstimate hfm d) ((continuous_id.sub continuous_const).pow 2)
    fun ρ ↦ ((memLp_scrambledEstimate hb hf d ρ).sub (memLp_const _)).integrable_sq

/-- **Subtracting an exactly integrated function does not change the variance**: if the
estimator of `g` equals `∫ g` for every scramble and all remainders in `[0,1)`, then the
scrambled estimators of `f` and `f - g` have the same variance. -/
theorem variance_scrambledLaw_sub_of_exact (hb : 0 < b) {s n : ℕ} (hn : n ≠ 0)
    {f g : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s))
    (hgm : Measurable g) (hg : MemLp g 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b)
    (hex : ∀ (ρ : Fin s → Scramble b D) (u : Fin n → Fin s → ℝ),
      (∀ i j, u i j ∈ Set.Ico (0 : ℝ) 1) →
      sampleMean n g (fun i ↦ scrambledPoint ρ (d i) (u i)) = ∫ x, g x ∂(uniformCube s)) :
    Var[fun x ↦ x; scrambledLaw f d] = Var[fun x ↦ x; scrambledLaw (f - g) d] := by
  rw [variance_scrambledLaw_eq_sum hb hn hfm hf d,
    variance_scrambledLaw_eq_sum hb hn (hfm.sub hgm) (hf.sub hg) d]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ ↦ integral_congr_ae ?_
  filter_upwards [ae_mem_cube_remLaw s n] with u hu
  have hsplit : scrambledEstimate f d ρ u =
      scrambledEstimate (f - g) d ρ u + sampleMean n g (fun i ↦ scrambledPoint ρ (d i) (u i)) := by
    unfold scrambledEstimate sampleMean
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    ring
  have hint : ∫ x, (f - g) x ∂(uniformCube s) =
      ∫ x, f x ∂(uniformCube s) - ∫ x, g x ∂(uniformCube s) :=
    integral_sub (hf.integrable one_le_two) (hg.integrable one_le_two)
  rw [hsplit, hex ρ u hu, hint]
  ring

/-- A point of `[0,1)^s` is within `b^{-R}` (sup distance) of the corner of its level-`R` cube,
and both lie in `[0,1]^s`. -/
theorem dist_corner_lt (hb : 1 < b) {s : ℕ} (R : ℕ) {x : Fin s → ℝ}
    (hx : ∀ j, x j ∈ Set.Ico (0 : ℝ) 1) {δ : ℝ} (hδ : (1 / (b : ℝ)) ^ R < δ) :
    dist x (fun j ↦ (boxIndex b (fun _ ↦ R) x j : ℝ) / (b : ℝ) ^ R) < δ ∧
      (fun j ↦ (boxIndex b (fun _ ↦ R) x j : ℝ) / (b : ℝ) ^ R) ∈
        Set.pi Set.univ fun _ ↦ Set.Icc (0 : ℝ) 1 := by
  have hb' : (0 : ℝ) < b := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have hbR : (0 : ℝ) < (b : ℝ) ^ R := pow_pos hb' R
  have hδ0 : 0 < δ := lt_of_le_of_lt (pow_nonneg (by positivity) R) hδ
  have hc : ∀ j, (boxIndex b (fun _ ↦ R) x j : ℝ) / (b : ℝ) ^ R ≤ x j ∧
      x j < (boxIndex b (fun _ ↦ R) x j : ℝ) / (b : ℝ) ^ R + 1 / (b : ℝ) ^ R := by
    intro j
    unfold boxIndex
    have h0 : 0 ≤ (b : ℝ) ^ R * x j := mul_nonneg hbR.le (hx j).1
    have h1 := Nat.floor_le h0
    have h2 := Nat.lt_floor_add_one ((b : ℝ) ^ R * x j)
    constructor
    · rw [div_le_iff₀ hbR]
      linarith
    · rw [← add_div, lt_div_iff₀ hbR]
      linarith
  refine ⟨(dist_pi_lt_iff hδ0).2 fun j ↦ ?_, fun j _ ↦ ⟨?_, ?_⟩⟩
  · rw [Real.dist_eq, abs_of_nonneg (by linarith [(hc j).1])]
    have : 1 / (b : ℝ) ^ R = (1 / (b : ℝ)) ^ R := by rw [one_div_pow]
    linarith [(hc j).2]
  · exact div_nonneg (Nat.cast_nonneg _) hbR.le
  · linarith [(hc j).1, (hx j).2]

/-- **Step functions are dense in `L²` of the cube**: every `f ∈ L²` is approximated in mean
square, to any `ε > 0`, by bounded step functions at every sufficiently fine level `R`. -/
theorem exists_stepFn_approx (hb : 1 < b) {s : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R ≥ R₀, ∃ (G : (Fin s → ℕ) → ℝ) (M : ℝ), (∀ a, |G a| ≤ M) ∧
      ∫ x, (f x - stepFn b R G x) ^ 2 ∂(uniformCube s) ≤ ε := by
  have := isProbabilityMeasure_uniformCube s
  have hb' : (0 : ℝ) < b := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have hf' : MemLp f (ENNReal.ofReal 2) (uniformCube s) := by
    rw [ENNReal.ofReal_ofNat]
    exact hf
  obtain ⟨h, hfh, hhL⟩ := hf'.exists_boundedContinuous_integral_rpow_sub_le two_pos
    (ε := ε / 4) (by positivity)
  rw [ENNReal.ofReal_ofNat] at hhL
  have hfh' : ∫ x, (f x - h x) ^ 2 ∂(uniformCube s) ≤ ε / 4 := by
    refine le_trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun x ↦ ?_))) hfh
    simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  set K : Set (Fin s → ℝ) := Set.pi Set.univ fun _ ↦ Set.Icc (0 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ ↦ isCompact_Icc
  have huc := hKc.uniformContinuousOn_of_continuous h.continuous.continuousOn
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuousOn_iff.1 huc (Real.sqrt (ε / 4))
    (Real.sqrt_pos.2 (by positivity))
  obtain ⟨R₀, hR₀⟩ := exists_pow_lt_of_lt_one hδ
    (show 1 / (b : ℝ) < 1 by rw [div_lt_one hb']; exact Nat.one_lt_cast.2 hb)
  refine ⟨R₀, fun R hR ↦ ⟨fun a ↦ h fun j ↦ (a j : ℝ) / (b : ℝ) ^ R, ‖h‖,
    fun a ↦ by rw [← Real.norm_eq_abs]; exact h.norm_coe_le_norm _, ?_⟩⟩
  have hRδ : (1 / (b : ℝ)) ^ R < δ := lt_of_le_of_lt
    (pow_le_pow_of_le_one (by positivity) (by rw [div_le_one hb']; exact (Nat.one_lt_cast.2 hb).le)
      hR) hR₀
  set g := stepFn b R fun a ↦ h fun j ↦ (a j : ℝ) / (b : ℝ) ^ R with hg
  have hgL : MemLp g 2 (uniformCube s) :=
    memLp_stepFn b R (M := ‖h‖) (fun a ↦ by rw [← Real.norm_eq_abs]; exact h.norm_coe_le_norm _) 2
  have hcube := ae_mem_cube_uniformCube s
  have hpt : ∀ᵐ x ∂(uniformCube s), (h x - g x) ^ 2 ≤ ε / 4 := by
    filter_upwards [hcube] with x hx
    obtain ⟨hd, hcK⟩ := dist_corner_lt hb R hx hRδ
    have hxK : x ∈ K := fun j _ ↦ ⟨(hx j).1, (hx j).2.le⟩
    have := hδh x hxK _ hcK hd
    rw [Real.dist_eq] at this
    have h2 : (h x - g x) ^ 2 ≤ Real.sqrt (ε / 4) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this.le 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hfhL := hf.sub hhL
  have hhgL := hhL.sub hgL
  calc ∫ x, (f x - g x) ^ 2 ∂(uniformCube s)
      ≤ ∫ x, (2 * (f x - h x) ^ 2 + 2 * (h x - g x) ^ 2) ∂(uniformCube s) := by
        refine integral_mono (hf.sub hgL).integrable_sq ?_ fun x ↦ ?_
        · exact (hfhL.integrable_sq.const_mul 2).add (hhgL.integrable_sq.const_mul 2)
        · nlinarith [sq_nonneg (f x - h x - (h x - g x))]
    _ = 2 * ∫ x, (f x - h x) ^ 2 ∂(uniformCube s) + 2 * ∫ x, (h x - g x) ^ 2 ∂(uniformCube s) := by
        have i1 : Integrable (fun x ↦ 2 * (f x - h x) ^ 2) (uniformCube s) :=
          hfhL.integrable_sq.const_mul 2
        have i2 : Integrable (fun x ↦ 2 * (h x - g x) ^ 2) (uniformCube s) :=
          hhgL.integrable_sq.const_mul 2
        rw [integral_add i1 i2, integral_const_mul, integral_const_mul]
    _ ≤ 2 * (ε / 4) + 2 * (ε / 4) := by
        have h3 : ∫ x, (h x - g x) ^ 2 ∂(uniformCube s) ≤ ε / 4 := by
          calc ∫ x, (h x - g x) ^ 2 ∂(uniformCube s) ≤ ∫ _x, ε / 4 ∂(uniformCube s) :=
                integral_mono_ae hhgL.integrable_sq (integrable_const _) hpt
            _ = ε / 4 := by rw [integral_const, probReal_univ, one_smul]
        linarith
    _ = ε := by ring

/-- **Scrambled `(0,m,s)`-nets are asymptotically better than Monte Carlo** (Owen 1997):
for a sequence of `(0,m,s)`-nets in base `b ≥ s - 1` (with `m` digits) and every measurable
`f ∈ L²`, `n Var(μ̂) → 0` as `m → ∞` (`n = b^m`), i.e. `Var(μ̂) = o(1/n)`. -/
theorem tendsto_pow_mul_variance_scrambledLaw (hb : 1 < b) {s : ℕ} (hs : 1 ≤ s)
    (hsb : s ≤ b + 1)
    (d : (m : ℕ) → Fin (b ^ m) → Fin s → Fin m → Fin b)
    (hnet : ∀ m, IsNet b 0 m fun i j ↦ digitPoint (d m i j) 0)
    {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s)) :
    Tendsto (fun m ↦ (b : ℝ) ^ m * Var[fun x ↦ x; scrambledLaw f (d m)]) atTop (𝓝 0) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have hU := isProbabilityMeasure_uniformCube s
  set C : ℝ := ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1) with hC
  have hC1 : 1 ≤ C := by
    refine one_le_pow₀ ?_
    rw [one_le_div hb1]
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R₀, hR₀⟩ := exists_stepFn_approx hb hf (ε := ε / (2 * C)) (by positivity)
  refine ⟨s * R₀, fun m hm ↦ ?_⟩
  set R := m / s with hRdef
  have hRR₀ : R₀ ≤ R := (Nat.le_div_iff_mul_le hs).2 (by rw [mul_comm]; exact hm)
  have hsR : s * R ≤ m := Nat.mul_div_le m s
  have hRm : R ≤ m := Nat.div_le_self m s
  obtain ⟨G, M, hG, hint⟩ := hR₀ R hRR₀
  set g := stepFn b R G with hg
  have hgm : Measurable g := measurable_stepFn b R G
  have hgL : MemLp g 2 (uniformCube s) := memLp_stepFn b R hG 2
  have hn : b ^ m ≠ 0 := (Nat.pow_pos hb0).ne'
  have hvar := variance_scrambledLaw_sub_of_exact hb0 hn hfm hf hgm hgL (d m)
    fun ρ u hu ↦ sampleMean_stepFn_scrambledPoint hb0 le_rfl hRm hsR (hnet m) hG ρ hu
  have hle := variance_scrambledLaw_le hb le_rfl (hnet m) hsb (hfm.sub hgm) (hf.sub hgL)
  have hVfg : Var[f - g; uniformCube s] ≤ ε / (2 * C) := by
    refine le_trans (variance_le_expectation_sq (hfm.sub hgm).aestronglyMeasurable) ?_
    exact le_trans (le_of_eq rfl) hint
  have hV0 : 0 ≤ Var[fun x ↦ x; scrambledLaw f (d m)] := variance_nonneg _ _
  have hbm : (0 : ℝ) < (b : ℝ) ^ m := pow_pos hb' m
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hbm.le hV0), hvar]
  rw [Nat.cast_pow] at hle
  calc (b : ℝ) ^ m * Var[fun x ↦ x; scrambledLaw (f - g) (d m)]
      ≤ (b : ℝ) ^ m * (C * Var[f - g; uniformCube s] / (b : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left hle hbm.le
    _ = C * Var[f - g; uniformCube s] := by field_simp
    _ ≤ C * (ε / (2 * C)) := mul_le_mul_of_nonneg_left hVfg (by linarith)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

end RQMCMarkov.OwenScrambling
