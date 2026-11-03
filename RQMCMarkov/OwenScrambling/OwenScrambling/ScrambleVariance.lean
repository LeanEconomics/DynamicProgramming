/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OwenScrambling.ScrambleGain
import Mathlib.Probability.Independence.Integration

/-!
# Variance of scrambled net quadrature (Owen 1997; post #2)

The scrambled-net estimator `μ̂ = (1/n) Σ_i f(X_i)`, `X_i = scrambledPoint ρ (d i) (u i)`, with
`ρ` uniform over the `s`-fold nested scrambles and the remainders `u ~ remLaw s n`
(i.i.d. `U[0,1)^s`), has law `scrambledLaw f d` (a `mixLaw`). We compute its variance exactly.

**Reduction to the grid.** With the cell averages `F = cellAvg f` and cell mean squares
`cellSq f`, independence of the remainders (`integral_remLaw_mul`) gives the moments for a fixed
scramble (`integral_scrambledEstimate`, `integral_sq_scrambledEstimate`); the cells tile the cube
(`sum_map_cellPoint`, `sum_integral_cellPoint`).

## Main results

* `integral_scrambledLaw` (**unbiasedness**, posts #1–#2): `E[μ̂] = ∫ f` for ANY digit points.
* `variance_eq_cellResVar_add` (**ANOVA–Haar decomposition**): `Var f = σ²_{>D} + Σ_{ℓ≠0} σ²_ℓ`,
  with the within-cell variance `cellResVar b D f ≥ 0` (`cellResVar_nonneg`, Jensen
  `cellAvg_sq_le`) and the Haar components `σ²_ℓ = haarVar (cellAvg f) ℓ ≥ 0`.
* `mixLaw_scrambledPoint_pair_eq` (**pair law of real scrambled points**, item (iii)): the joint
  law of two scrambled points depends only on the common-digit counts of their coordinates.
* `variance_scrambledLaw` (**Owen's variance formula**):
  `Var(μ̂) = n⁻¹ (σ²_{>D} + Σ_{ℓ ≠ 0} Γ_ℓ σ²_ℓ)` for any digit points, `Γ_ℓ = gainCoeff b d ℓ`.
* `variance_scrambledLaw_le` (**never much worse than MC**, Owen 1997): for a `(0,m,s)`-net with
  `s ≤ b + 1`, `Var(μ̂) ≤ (b/(b-1))^{s-1} σ²/n`; `variance_scrambledLaw_le_exp_one`: `≤ e σ²/n`
  when `s ≤ b` (`pow_div_sub_one_le_exp_one`).
* Tools: `integral_mixLaw`, `isProbabilityMeasure_mixLaw`, `memLp_id_mixLaw`,
  `isProbabilityMeasure_remLaw`, `memLp_comp_cellPoint`, `memLp_scrambledEstimate`.

The `o(1/n)` statement is in `ScrambleAsymptotic`; the CLT in `LohCLT`.

**Reading.** Variances are those of the law `scrambledLaw f d` on `ℝ` (`Var[fun x ↦ x; ·]`); `f`
is measurable and in `L²(U[0,1)^s)`; the digit points have `D` digits (`D = m` for a net of
`b^m` points). The bound is stated for `t = 0`, the case of the post's claim (Loh 2003).
-/

namespace RQMCMarkov.OwenScrambling

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {b D : ℕ}

/-- The real point of an `s`-dimensional digit point `y` with remainders `u`. -/
noncomputable def cellPoint {s : ℕ} (y : Fin s → Fin D → Fin b) (u : Fin s → ℝ) : Fin s → ℝ :=
  fun j ↦ digitPoint (y j) (u j)

/-- A scrambled point is the cell point of the scrambled digit point. -/
theorem scrambledPoint_eq_cellPoint {s : ℕ} (ρ : Fin s → Scramble b D)
    (c : Fin s → Fin D → Fin b) (u : Fin s → ℝ) :
    scrambledPoint ρ c u = cellPoint (scrambleVec ρ c) u := rfl

/-- Measurability of a cell point in its remainders. -/
theorem measurable_cellPoint {s : ℕ} (y : Fin s → Fin D → Fin b) : Measurable (cellPoint y) :=
  measurable_pi_iff.2 fun j ↦ (measurable_digitPoint _).comp (measurable_pi_apply j)

/-- **Pair law of scrambled points depends only on the common digits** (Owen 1997, item (iii),
real points): if the digit points `(c, c')` and `(e, e')` have the same numbers of common leading
digits in every coordinate, then the scrambled pairs `(X, X')` (independent uniform scrambles,
independent `U[0,1)^s` remainders `u, v`) have the same joint law. -/
theorem mixLaw_scrambledPoint_pair_eq (hb : 1 < b) {s : ℕ} {c c' e e' : Fin s → Fin D → Fin b}
    (hk : ∀ j, commonPrefix (c j) (c' j) = commonPrefix (e j) (e' j)) :
    mixLaw ((uniformCube s).prod (uniformCube s))
      (fun (ρ : Fin s → Scramble b D) uv ↦
        (scrambledPoint ρ c uv.1, scrambledPoint ρ c' uv.2)) =
    mixLaw ((uniformCube s).prod (uniformCube s))
      (fun (ρ : Fin s → Scramble b D) uv ↦
        (scrambledPoint ρ e uv.1, scrambledPoint ρ e' uv.2)) := by
  set G : (Fin s → Fin D → Fin b) × (Fin s → Fin D → Fin b) →
      Measure ((Fin s → ℝ) × (Fin s → ℝ)) := fun p ↦ ((uniformCube s).prod (uniformCube s)).map
      (fun uv ↦ (cellPoint p.1 uv.1, cellPoint p.2 uv.2)) with hG
  have hsum : ∀ x x' : Fin s → Fin D → Fin b,
      ∑ ρ : Fin s → Scramble b D, ((uniformCube s).prod (uniformCube s)).map
        (fun uv ↦ (scrambledPoint ρ x uv.1, scrambledPoint ρ x' uv.2)) =
      ∑ p, (Finset.univ.filter fun ρ : Fin s → Scramble b D ↦
        scrambleVec ρ x = p.1 ∧ scrambleVec ρ x' = p.2).card • G p := by
    intro x x'
    rw [← Finset.sum_fiberwise Finset.univ (fun ρ ↦ (scrambleVec ρ x, scrambleVec ρ x'))
      (fun ρ ↦ ((uniformCube s).prod (uniformCube s)).map
        (fun uv ↦ (scrambledPoint ρ x uv.1, scrambledPoint ρ x' uv.2)))]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.sum_congr rfl fun ρ hρ ↦ by
      obtain ⟨e1, e2⟩ := Prod.mk.inj (Finset.mem_filter.1 hρ).2
      change ((uniformCube s).prod (uniformCube s)).map
        (fun uv ↦ (cellPoint (scrambleVec ρ x) uv.1, cellPoint (scrambleVec ρ x') uv.2)) = G p
      rw [e1, e2], Finset.sum_const]
    congr 1
    exact congrArg Finset.card (Finset.filter_congr fun ρ _ ↦ Prod.ext_iff)
  have hcard : ∀ p : (Fin s → Fin D → Fin b) × (Fin s → Fin D → Fin b),
      (Finset.univ.filter fun ρ : Fin s → Scramble b D ↦
        scrambleVec ρ c = p.1 ∧ scrambleVec ρ c' = p.2).card =
      (Finset.univ.filter fun ρ : Fin s → Scramble b D ↦
        scrambleVec ρ e = p.1 ∧ scrambleVec ρ e' = p.2).card := by
    intro p
    have h1 := card_scrambleVec_pair hb c c' p.1 p.2
    have h2 := card_scrambleVec_pair hb e e' p.1 p.2
    simp only [hk] at h1
    exact_mod_cast h1.trans h2.symm
  unfold mixLaw
  rw [hsum c c', hsum e e']
  simp only [hcard]

/-- The cells `[cellVal x / b^D, (cellVal x + 1)/b^D)` tile `[0,1)`:
`Σ_x U[0,1).map (digitPoint x) = b^D • U[0,1)`. -/
theorem sum_map_digitPoint (hb : 0 < b) :
    ∑ x : Fin D → Fin b, uniformIco.map (digitPoint x) = ((b ^ D : ℕ) : ℝ≥0∞) • uniformIco := by
  have hbD : b ^ D ≠ 0 := (Nat.pow_pos hb).ne'
  have h1 : ∑ y : Fin D → Fin b, uniformIco.map (digitPoint y) =
      ∑ i : Fin (b ^ D), uniformIco.map (stratumMap (b ^ D) i) := by
    rw [← (cellFin_bijective (D := D) hb).sum_comp
      (fun i : Fin (b ^ D) ↦ uniformIco.map (stratumMap (b ^ D) i))]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    congr 1
    funext u
    rw [digitPoint_eq_stratumMap]
    rfl
  rw [h1, sum_map_stratumMap hbD]

/-- The cells of the digit grid tile `[0,1)^s`:
`Σ_y U[0,1)^s.map (cellPoint y) = b^{sD} • U[0,1)^s`. -/
theorem sum_map_cellPoint (hb : 0 < b) (s : ℕ) :
    ∑ y : Fin s → Fin D → Fin b, (uniformCube s).map (cellPoint y) =
      (((b ^ D) ^ s : ℕ) : ℝ≥0∞) • uniformCube s := by
  have := isProbabilityMeasure_uniformIco
  have hmap : ∀ y : Fin s → Fin D → Fin b, (uniformCube s).map (cellPoint y) =
      Measure.pi fun j ↦ uniformIco.map (digitPoint (y j)) := fun y ↦
    Measure.pi_map_pi (fun j ↦ (measurable_digitPoint _).aemeasurable)
  simp only [hmap]
  have hpi : uniformCube s = ((((b ^ D) ^ s : ℕ) : ℝ≥0∞))⁻¹ •
      ∑ y : Fin s → Fin D → Fin b, Measure.pi fun j ↦ uniformIco.map (digitPoint (y j)) := by
    refine Measure.pi_eq fun S hS ↦ ?_
    rw [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun y _ ↦ Measure.pi_pi _ _)]
    rw [← Fintype.prod_sum (fun j (x : Fin D → Fin b) ↦ uniformIco.map (digitPoint x) (S j))]
    have h2 : ∀ j, ∑ x : Fin D → Fin b, uniformIco.map (digitPoint x) (S j) =
        ((b ^ D : ℕ) : ℝ≥0∞) * uniformIco (S j) := by
      intro j
      rw [← Measure.finsetSum_apply, sum_map_digitPoint hb, Measure.smul_apply, smul_eq_mul]
    rw [Finset.prod_congr rfl (fun j _ ↦ h2 j), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← mul_assoc, Nat.cast_pow, ENNReal.inv_mul_cancel,
      one_mul]
    · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.pow_pos hb).ne')
    · exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  rw [hpi, smul_smul, ENNReal.mul_inv_cancel, one_smul]
  · exact Nat.cast_ne_zero.2 (pow_ne_zero _ (Nat.pow_pos hb).ne')
  · exact ENNReal.natCast_ne_top _

/-- The law of one cell point is dominated by `b^{sD} • U[0,1)^s`. -/
theorem map_cellPoint_le (hb : 0 < b) {s : ℕ} (y : Fin s → Fin D → Fin b) :
    (uniformCube s).map (cellPoint y) ≤ (((b ^ D) ^ s : ℕ) : ℝ≥0∞) • uniformCube s := by
  rw [← sum_map_cellPoint hb s]
  exact Finset.single_le_sum (f := fun y ↦ (uniformCube s).map (cellPoint y))
    (fun _ _ ↦ Measure.zero_le _) (Finset.mem_univ y)

/-- `g ∈ L^p(U[0,1)^s)` restricted to a cell is in `L^p`. -/
theorem memLp_comp_cellPoint (hb : 0 < b) {s : ℕ} {p : ℝ≥0∞} {g : (Fin s → ℝ) → ℝ}
    (hg : MemLp g p (uniformCube s)) (y : Fin s → Fin D → Fin b) :
    MemLp (fun u ↦ g (cellPoint y u)) p (uniformCube s) := by
  have h1 : MemLp g p ((uniformCube s).map (cellPoint y)) :=
    (hg.smul_measure (ENNReal.natCast_ne_top _)).mono_measure (map_cellPoint_le hb y)
  exact h1.comp_of_map (measurable_cellPoint y).aemeasurable

/-- **Integrating cell by cell**: `Σ_y ∫ g(cellPoint y u) du = b^{sD} ∫ g`. -/
theorem sum_integral_cellPoint (hb : 0 < b) {s : ℕ} {g : (Fin s → ℝ) → ℝ}
    (hg : Integrable g (uniformCube s)) :
    ∑ y : Fin s → Fin D → Fin b, ∫ u, g (cellPoint y u) ∂(uniformCube s) =
      ((b : ℝ) ^ D) ^ s * ∫ x, g x ∂(uniformCube s) := by
  have hgi : ∀ y : Fin s → Fin D → Fin b, Integrable g ((uniformCube s).map (cellPoint y)) :=
    fun y ↦ (hg.smul_measure (ENNReal.natCast_ne_top _)).mono_measure (map_cellPoint_le hb y)
  have e : ∀ y : Fin s → Fin D → Fin b, ∫ u, g (cellPoint y u) ∂(uniformCube s) =
      ∫ x, g x ∂((uniformCube s).map (cellPoint y)) := fun y ↦
    (integral_map (measurable_cellPoint y).aemeasurable (hgi y).aestronglyMeasurable).symm
  rw [Finset.sum_congr rfl fun y _ ↦ e y, ← integral_finsetSum_measure fun y _ ↦ hgi y,
    sum_map_cellPoint hb s, integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul,
    Nat.cast_pow, Nat.cast_pow]

/-- The law of the remainders: one independent `U[0,1)^s` vector for each of the `n` points. -/
noncomputable abbrev remLaw (s n : ℕ) : Measure (Fin n → Fin s → ℝ) :=
  Measure.pi fun _ : Fin n ↦ uniformCube s

/-- `remLaw s n` is a probability measure. -/
theorem isProbabilityMeasure_remLaw (s n : ℕ) : IsProbabilityMeasure (remLaw s n) := by
  have := isProbabilityMeasure_uniformCube s
  exact Measure.pi.instIsProbabilityMeasure _

/-- The remainder of point `i` is `U[0,1)^s`. -/
theorem measurePreserving_remLaw_eval (s : ℕ) {n : ℕ} (i : Fin n) :
    MeasurePreserving (Function.eval i) (remLaw s n) (uniformCube s) := by
  have := isProbabilityMeasure_uniformCube s
  exact measurePreserving_eval (fun _ : Fin n ↦ uniformCube s) i

/-- `E[g(u_i)] = ∫ g` over the cube. -/
theorem integral_remLaw_eval {s n : ℕ} {g : (Fin s → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (uniformCube s)) (i : Fin n) :
    ∫ u, g (u i) ∂(remLaw s n) = ∫ x, g x ∂(uniformCube s) := by
  have hmp := measurePreserving_remLaw_eval s i
  rw [← hmp.map_eq] at hg ⊢
  exact (integral_map hmp.measurable.aemeasurable hg).symm

/-- `g ∈ L^p` of the cube gives `u ↦ g(u_i) ∈ L^p` of the remainders. -/
theorem memLp_remLaw_eval {s n : ℕ} {p : ℝ≥0∞} {g : (Fin s → ℝ) → ℝ}
    (hg : MemLp g p (uniformCube s)) (i : Fin n) :
    MemLp (fun u : Fin n → Fin s → ℝ ↦ g (u i)) p (remLaw s n) := by
  have hmp := measurePreserving_remLaw_eval s i
  rw [← hmp.map_eq] at hg
  exact hg.comp_of_map hmp.measurable.aemeasurable

/-- **Independent remainders**: `E[g(u_i) h(u_{i'})] = (∫ g)(∫ h)` for `i ≠ i'`. -/
theorem integral_remLaw_mul {s n : ℕ} {g h : (Fin s → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (uniformCube s)) (hh : AEStronglyMeasurable h (uniformCube s))
    {i i' : Fin n} (hii : i ≠ i') :
    ∫ u, g (u i) * h (u i') ∂(remLaw s n) =
      (∫ x, g x ∂(uniformCube s)) * ∫ x, h x ∂(uniformCube s) := by
  have := isProbabilityMeasure_uniformCube s
  have hind : iIndepFun (fun (k : Fin n) (u : Fin n → Fin s → ℝ) ↦ u k) (remLaw s n) :=
    iIndepFun_pi (X := fun _ (x : Fin s → ℝ) ↦ x) fun _ ↦ aemeasurable_id
  have hpair := hind.indepFun hii
  have hmi := measurePreserving_remLaw_eval s i
  have hmi' := measurePreserving_remLaw_eval s i'
  have hg' : AEStronglyMeasurable g ((remLaw s n).map (fun u : Fin n → Fin s → ℝ ↦ u i)) := by
    rw [show (fun u : Fin n → Fin s → ℝ ↦ u i) = Function.eval i from rfl, hmi.map_eq]
    exact hg
  have hh' : AEStronglyMeasurable h ((remLaw s n).map (fun u : Fin n → Fin s → ℝ ↦ u i')) := by
    rw [show (fun u : Fin n → Fin s → ℝ ↦ u i') = Function.eval i' from rfl, hmi'.map_eq]
    exact hh
  have h1 := hpair.integral_comp_mul_comp (f := g) (g := h) hmi.measurable.aemeasurable
    hmi'.measurable.aemeasurable hg' hh'
  calc ∫ u, g (u i) * h (u i') ∂(remLaw s n)
      = ∫ u, ((g ∘ fun u : Fin n → Fin s → ℝ ↦ u i) *
          (h ∘ fun u : Fin n → Fin s → ℝ ↦ u i')) u ∂(remLaw s n) := rfl
    _ = (∫ u, (g ∘ fun u : Fin n → Fin s → ℝ ↦ u i) u ∂(remLaw s n)) *
          ∫ u, (h ∘ fun u : Fin n → Fin s → ℝ ↦ u i') u ∂(remLaw s n) := h1
    _ = (∫ x, g x ∂(uniformCube s)) * ∫ x, h x ∂(uniformCube s) := by
        rw [← integral_remLaw_eval hg i, ← integral_remLaw_eval hh i']
        rfl

/-- The **cell average** `F(y) = ∫ f(cellPoint y u) du` of `f` over the cell of `y`. -/
noncomputable def cellAvg {s : ℕ} (f : (Fin s → ℝ) → ℝ) (y : Fin s → Fin D → Fin b) : ℝ :=
  ∫ u, f (cellPoint y u) ∂(uniformCube s)

/-- The **cell mean square** `∫ f(cellPoint y u)² du`. -/
noncomputable def cellSq {s : ℕ} (f : (Fin s → ℝ) → ℝ) (y : Fin s → Fin D → Fin b) : ℝ :=
  ∫ u, f (cellPoint y u) ^ 2 ∂(uniformCube s)

/-- **Jensen in a cell**: `F(y)² ≤ ∫ f(cellPoint y u)² du`. -/
theorem cellAvg_sq_le (hb : 0 < b) {s : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) (y : Fin s → Fin D → Fin b) :
    cellAvg f y ^ 2 ≤ cellSq f y := by
  have := isProbabilityMeasure_uniformCube s
  have hL := memLp_comp_cellPoint hb hf y
  have hv := variance_nonneg (fun u ↦ f (cellPoint y u)) (uniformCube s)
  rw [variance_eq_sub hL] at hv
  unfold cellAvg cellSq
  have e : ∫ u, ((fun u ↦ f (cellPoint y u)) ^ 2) u ∂(uniformCube s) =
      ∫ u, f (cellPoint y u) ^ 2 ∂(uniformCube s) := rfl
  linarith

/-- The **scrambled-net estimator** `(1/n) Σ_i f(X_i)` with `X_i = scrambledPoint ρ (d i) (u i)`.
-/
noncomputable def scrambledEstimate {s n : ℕ} (f : (Fin s → ℝ) → ℝ)
    (d : Fin n → Fin s → Fin D → Fin b) (ρ : Fin s → Scramble b D)
    (u : Fin n → Fin s → ℝ) : ℝ :=
  sampleMean n f fun i ↦ scrambledPoint ρ (d i) (u i)

/-- The **law of the scrambled-net estimator**: uniform independent nested scrambles in the `s`
coordinates, independent `U[0,1)^s` remainders. -/
noncomputable def scrambledLaw {s n : ℕ} (f : (Fin s → ℝ) → ℝ)
    (d : Fin n → Fin s → Fin D → Fin b) : Measure ℝ :=
  mixLaw (remLaw s n) (scrambledEstimate f d)

/-- The estimator for a fixed scramble is in `L²` of the remainders. -/
theorem memLp_scrambledEstimate (hb : 0 < b) {s n : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b)
    (ρ : Fin s → Scramble b D) : MemLp (scrambledEstimate f d ρ) 2 (remLaw s n) := by
  unfold scrambledEstimate sampleMean
  refine MemLp.const_mul ?_ _
  exact memLp_finsetSum _ fun i _ ↦ memLp_remLaw_eval (memLp_comp_cellPoint hb hf _) i

/-- The estimator for a fixed scramble is measurable when `f` is. -/
theorem measurable_scrambledEstimate {s n : ℕ} {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f)
    (d : Fin n → Fin s → Fin D → Fin b) (ρ : Fin s → Scramble b D) :
    Measurable (scrambledEstimate f d ρ) := by
  unfold scrambledEstimate sampleMean
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun i _ ↦ hfm.comp ?_
  exact (measurable_scrambledPoint ρ (d i)).comp (measurable_pi_apply i)

/-- First moment for a fixed scramble: `E_u[μ̂] = (1/n) Σ_i F(σ d_i)`. -/
theorem integral_scrambledEstimate (hb : 0 < b) {s n : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b)
    (ρ : Fin s → Scramble b D) :
    ∫ u, scrambledEstimate f d ρ u ∂(remLaw s n) =
      (n : ℝ)⁻¹ * ∑ i, cellAvg f (scrambleVec ρ (d i)) := by
  unfold scrambledEstimate sampleMean
  beta_reduce
  rw [integral_const_mul, integral_finsetSum (f := fun i (u : Fin n → Fin s → ℝ) ↦
    f (scrambledPoint ρ (d i) (u i))) _ fun i _ ↦
    (memLp_remLaw_eval (memLp_comp_cellPoint hb hf _) i).integrable one_le_two]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact integral_remLaw_eval (g := fun v ↦ f (cellPoint (scrambleVec ρ (d i)) v))
    (memLp_comp_cellPoint hb hf _).aestronglyMeasurable i

/-- Second moment for a fixed scramble:
`E_u[μ̂²] = n⁻² (Σ_i (∫_cell f² - F²)(σ d_i) + (Σ_i F(σ d_i))²)`. -/
theorem integral_sq_scrambledEstimate (hb : 0 < b) {s n : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b)
    (ρ : Fin s → Scramble b D) :
    ∫ u, scrambledEstimate f d ρ u ^ 2 ∂(remLaw s n) =
      ((n : ℝ)⁻¹) ^ 2 * (∑ i, (cellSq f (scrambleVec ρ (d i)) -
        cellAvg f (scrambleVec ρ (d i)) ^ 2) + (∑ i, cellAvg f (scrambleVec ρ (d i))) ^ 2) := by
  set c : Fin n → Fin s → Fin D → Fin b := fun i ↦ scrambleVec ρ (d i) with hc
  set g : Fin n → (Fin n → Fin s → ℝ) → ℝ := fun i u ↦ f (cellPoint (c i) (u i)) with hg
  have hgL : ∀ i, MemLp (g i) 2 (remLaw s n) := fun i ↦
    memLp_remLaw_eval (memLp_comp_cellPoint hb hf _) i
  have hest : ∀ u, scrambledEstimate f d ρ u ^ 2 =
      ((n : ℝ)⁻¹) ^ 2 * ∑ i, ∑ i', g i u * g i' u := by
    intro u
    unfold scrambledEstimate sampleMean
    rw [mul_pow, sq (∑ i, _), Finset.sum_mul_sum]
    rfl
  have hpair : ∀ i i', ∫ u, g i u * g i' u ∂(remLaw s n) =
      cellAvg f (c i) * cellAvg f (c i') +
        if i = i' then cellSq f (c i) - cellAvg f (c i) ^ 2 else 0 := by
    intro i i'
    by_cases hii : i = i'
    · subst hii
      rw [ite_eq_left rfl]
      have e : ∫ u, g i u * g i u ∂(remLaw s n) = cellSq f (c i) := by
        unfold cellSq
        rw [← integral_remLaw_eval (g := fun v ↦ f (cellPoint (c i) v) ^ 2)
          ((memLp_comp_cellPoint hb hf (c i)).integrable_sq.aestronglyMeasurable) i]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
        simp only [hg]
        ring
      rw [e]
      ring
    · rw [ite_eq_right hii, add_zero]
      exact integral_remLaw_mul (memLp_comp_cellPoint hb hf (c i)).aestronglyMeasurable
        (memLp_comp_cellPoint hb hf (c i')).aestronglyMeasurable hii
  rw [integral_congr_ae (Filter.Eventually.of_forall hest), integral_const_mul,
    integral_finsetSum (f := fun i u ↦ ∑ i', g i u * g i' u) _ fun i _ ↦
      integrable_finsetSum _ fun i' _ ↦ (hgL i).integrable_mul (hgL i')]
  rw [Finset.sum_congr rfl fun i _ ↦ integral_finsetSum (f := fun i' u ↦ g i u * g i' u) _
    fun i' _ ↦ (hgL i).integrable_mul (hgL i')]
  simp only [hpair, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [sq (∑ i, cellAvg f (c i)), Finset.sum_mul_sum]
  ring

/-- Integrals against a mixture law: `∫ g d(mixLaw Q Φ) = (#R)⁻¹ Σ_ρ ∫ g(Φ ρ u) dQ(u)`. -/
theorem integral_mixLaw {R E : Type*} [Fintype R] [MeasurableSpace E] {Q : Measure E}
    {Φ : R → E → ℝ} (hΦ : ∀ ρ, Measurable (Φ ρ)) {g : ℝ → ℝ} (hg : Continuous g)
    (hint : ∀ ρ, Integrable (fun u ↦ g (Φ ρ u)) Q) :
    ∫ x, g x ∂(mixLaw Q Φ) = (Fintype.card R : ℝ)⁻¹ * ∑ ρ, ∫ u, g (Φ ρ u) ∂Q := by
  have hgi : ∀ ρ, Integrable g (Q.map (Φ ρ)) := fun ρ ↦
    (integrable_map_measure hg.aestronglyMeasurable (hΦ ρ).aemeasurable).2 (hint ρ)
  unfold mixLaw
  rw [integral_smul_measure, integral_finsetSum_measure fun ρ _ ↦ hgi ρ, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun ρ _ ↦ integral_map (hΦ ρ).aemeasurable hg.aestronglyMeasurable

/-- A mixture of probability laws is a probability law. -/
theorem isProbabilityMeasure_mixLaw {R E F : Type*} [Fintype R] [Nonempty R] [MeasurableSpace E]
    [MeasurableSpace F] {Q : Measure E} [IsProbabilityMeasure Q] {Φ : R → E → F}
    (hΦ : ∀ ρ, Measurable (Φ ρ)) : IsProbabilityMeasure (mixLaw Q Φ) := by
  refine ⟨?_⟩
  unfold mixLaw
  rw [Measure.smul_apply, Measure.finsetSum_apply,
    Finset.sum_congr rfl fun ρ _ ↦ by rw [Measure.map_apply (hΦ ρ) MeasurableSet.univ,
      Set.preimage_univ, measure_univ], Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, smul_eq_mul, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)]

/-- The identity is in `L²` of a mixture of `L²` laws. -/
theorem memLp_id_mixLaw {R E : Type*} [Fintype R] [Nonempty R] [MeasurableSpace E] {Q : Measure E}
    {Φ : R → E → ℝ} (hΦ : ∀ ρ, Measurable (Φ ρ)) (hL : ∀ ρ, MemLp (Φ ρ) 2 Q) :
    MemLp (fun x : ℝ ↦ x) 2 (mixLaw Q Φ) := by
  refine (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 ?_
  unfold mixLaw
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 Fintype.card_ne_zero))
  rw [integrable_finsetSum_measure]
  intro ρ _
  exact (integrable_map_measure (continuous_pow 2).aestronglyMeasurable
    (hΦ ρ).aemeasurable).2 (hL ρ).integrable_sq

/-- The number of `s`-dimensional nested scrambles. -/
theorem card_scramble_pi (s : ℕ) :
    (Fintype.card (Fin s → Scramble b D) : ℝ) = (Fintype.card (Scramble b D) : ℝ) ^ s := by
  rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

/-- **The scrambled-net estimator is unbiased** (Owen 1995): for ANY digit points `d`
(`n ≥ 1`) and every measurable `f ∈ L²(U[0,1)^s)`, `E[μ̂] = ∫ f`. -/
theorem integral_scrambledLaw (hb : 0 < b) {s n : ℕ} (hn : n ≠ 0) {f : (Fin s → ℝ) → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b) :
    ∫ x, x ∂(scrambledLaw f d) = ∫ x, f x ∂(uniformCube s) := by
  have hR : (0 : ℝ) < (Fintype.card (Scramble b D) : ℝ) ^ s :=
    pow_pos (Nat.cast_pos.2 Fintype.card_pos) s
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ s := pow_pos (pow_pos hb' D) s
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  unfold scrambledLaw
  rw [integral_mixLaw (g := fun x ↦ x) (measurable_scrambledEstimate hfm d) continuous_id
    fun ρ ↦ (memLp_scrambledEstimate hb hf d ρ).integrable one_le_two, card_scramble_pi]
  simp only [integral_scrambledEstimate hb hf d]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [sum_scrambleVec hb _ (cellAvg f)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold cellAvg
  rw [sum_integral_cellPoint hb (hf.integrable one_le_two)]
  field_simp

/-- The **within-cell variance** `b^{-sD} Σ_y (∫_cell f² - F(y)²)`: the part of `Var f` at
resolution finer than `D` digits in some coordinate. -/
noncomputable def cellResVar (b D : ℕ) {s : ℕ} (f : (Fin s → ℝ) → ℝ) : ℝ :=
  (∑ y : Fin s → Fin D → Fin b, (cellSq f y - cellAvg f y ^ 2)) / ((b : ℝ) ^ D) ^ s

/-- The within-cell variance is nonnegative. -/
theorem cellResVar_nonneg (hb : 0 < b) {s : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) : 0 ≤ cellResVar b D f :=
  div_nonneg (Finset.sum_nonneg fun y _ ↦ sub_nonneg.2 (cellAvg_sq_le hb hf y))
    (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)

/-- **ANOVA–Haar decomposition of the variance** (Owen 1997):
`Var f = σ²_{>D} + Σ_{ℓ ≠ 0} σ²_ℓ`, the within-cell variance plus the base-`b` Haar components
`σ²_ℓ = haarVar F ℓ` of the cell averages `F`. -/
theorem variance_eq_cellResVar_add (hb : 0 < b) {s : ℕ} {f : (Fin s → ℝ) → ℝ}
    (hf : MemLp f 2 (uniformCube s)) :
    Var[f; uniformCube s] = cellResVar b D f +
      ∑ ℓ ∈ (Finset.univ : Finset (Fin s → Fin (D + 1))).erase 0,
        haarVar (cellAvg (b := b) f) ℓ := by
  have := isProbabilityMeasure_uniformCube s
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ s := pow_pos (pow_pos hb' D) s
  have hsum := sum_haarVar hb (cellAvg f (b := b) (D := D))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), haarVar_zero] at hsum
  have h1 : ∑ y : Fin s → Fin D → Fin b, cellSq f y =
      ((b : ℝ) ^ D) ^ s * ∫ x, f x ^ 2 ∂(uniformCube s) :=
    sum_integral_cellPoint hb (g := fun x ↦ f x ^ 2) hf.integrable_sq
  have h2 : ∑ y : Fin s → Fin D → Fin b, cellAvg f y =
      ((b : ℝ) ^ D) ^ s * ∫ x, f x ∂(uniformCube s) :=
    sum_integral_cellPoint hb (hf.integrable one_le_two)
  rw [variance_eq_sub hf]
  unfold cellResVar
  rw [Finset.sum_sub_distrib, sub_div, h1]
  have e : ∑ ℓ ∈ (Finset.univ : Finset (Fin s → Fin (D + 1))).erase 0,
      haarVar (cellAvg (b := b) f) ℓ =
      (∑ y : Fin s → Fin D → Fin b, cellAvg f y ^ 2) / ((b : ℝ) ^ D) ^ s -
        ((∑ y : Fin s → Fin D → Fin b, cellAvg f y) / ((b : ℝ) ^ D) ^ s) ^ 2 := by linarith
  rw [e, h2]
  change ∫ x, f x ^ 2 ∂(uniformCube s) - (∫ x, f x ∂(uniformCube s)) ^ 2 = _
  field_simp
  ring

/-- **Owen's variance formula for scrambled nets** (Owen 1997): for any digit points `d`
(`n ≥ 1`) and measurable `f ∈ L²`,
`Var(μ̂) = n⁻¹ (σ²_{>D} + Σ_{ℓ ≠ 0} Γ_ℓ σ²_ℓ)`, with the gain coefficients `Γ_ℓ` of the point
set and the Haar components `σ²_ℓ` of `f`. -/
theorem variance_scrambledLaw (hb : 1 < b) {s n : ℕ} (hn : n ≠ 0) {f : (Fin s → ℝ) → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s)) (d : Fin n → Fin s → Fin D → Fin b) :
    Var[fun x ↦ x; scrambledLaw f d] = (n : ℝ)⁻¹ * (cellResVar b D f +
      ∑ ℓ ∈ (Finset.univ : Finset (Fin s → Fin (D + 1))).erase 0,
        gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ) := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hR : (0 : ℝ) < (Fintype.card (Scramble b D) : ℝ) ^ s :=
    pow_pos (Nat.cast_pos.2 Fintype.card_pos) s
  have hb' : (0 : ℝ) < b := Nat.cast_pos.2 hb0
  have hbD : (0 : ℝ) < ((b : ℝ) ^ D) ^ s := pow_pos (pow_pos hb' D) s
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hQ := isProbabilityMeasure_remLaw s n
  have hP := isProbabilityMeasure_mixLaw (Q := remLaw s n)
    (measurable_scrambledEstimate hfm d (b := b) (D := D))
  have hmean := integral_scrambledLaw hb0 hn hfm hf d
  have hL := memLp_id_mixLaw (measurable_scrambledEstimate hfm d)
    (memLp_scrambledEstimate hb0 hf d)
  unfold scrambledLaw at hmean hP hL ⊢
  rw [variance_eq_sub hL]
  change ∫ x, x ^ 2 ∂_ - (∫ x, x ∂_) ^ 2 = _
  rw [hmean, integral_mixLaw (g := fun x ↦ x ^ 2) (measurable_scrambledEstimate hfm d)
    (continuous_pow 2) fun ρ ↦ (memLp_scrambledEstimate hb0 hf d ρ).integrable_sq,
    card_scramble_pi]
  simp only [integral_sq_scrambledEstimate hb0 hf d]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
  simp only [sum_scrambleVec hb0 _ (fun y ↦ cellSq f y - cellAvg f y ^ 2)]
  have hsq := sum_sq_sum_scrambleVec hb d (cellAvg f)
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin s → Fin (D + 1)))
    (fun ℓ ↦ gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ) (Finset.mem_univ 0)
  rw [gainCoeff_zero hb hn, haarVar_zero] at hsplit
  have h2 : ∑ y : Fin s → Fin D → Fin b, cellAvg f y =
      ((b : ℝ) ^ D) ^ s * ∫ x, f x ∂(uniformCube s) :=
    sum_integral_cellPoint hb0 (hf.integrable one_le_two)
  rw [h2] at hsplit
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold cellResVar
  rw [show (∑ ρ : Fin s → Scramble b D, (∑ i, cellAvg f (scrambleVec ρ (d i))) ^ 2) =
    (Fintype.card (Scramble b D) : ℝ) ^ s *
      (n * ∑ ℓ, gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ) by
      rw [← hsq]
      field_simp, ← hsplit]
  field_simp
  ring

/-- The ratio `(b/(b-1))^{s-1}` is at most `e` when `s ≤ b`. -/
theorem pow_div_sub_one_le_exp_one (hb : 1 < b) {s : ℕ} (hsb : s ≤ b) :
    ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1) ≤ Real.exp 1 := by
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have ha : (b : ℝ) / ((b : ℝ) - 1) = 1 / ((b : ℝ) - 1) + 1 := by
    field_simp
    ring
  have h1 : (b : ℝ) / ((b : ℝ) - 1) ≤ Real.exp (1 / ((b : ℝ) - 1)) := by
    rw [ha]
    exact Real.add_one_le_exp _
  have h0 : (0 : ℝ) ≤ (b : ℝ) / ((b : ℝ) - 1) := div_nonneg (Nat.cast_nonneg _) hb1.le
  calc ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1) ≤ Real.exp (1 / ((b : ℝ) - 1)) ^ (s - 1) :=
        pow_le_pow_left₀ h0 h1 _
    _ = Real.exp (((s - 1 : ℕ) : ℝ) * (1 / ((b : ℝ) - 1))) := by
        rw [← Real.exp_nat_mul]
    _ ≤ Real.exp 1 := by
        refine Real.exp_le_exp.2 ?_
        have hs : ((s - 1 : ℕ) : ℝ) ≤ (b : ℝ) - 1 := by
          have : ((s - 1 : ℕ) : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := Nat.cast_le.2 (by omega)
          rwa [Nat.cast_sub hb.le, Nat.cast_one] at this
        rw [mul_one_div, div_le_one hb1]
        exact hs

/-- **Scrambled `(0,m,s)`-nets never do much worse than Monte Carlo** (Owen 1997,
`s ≤ b + 1`): `Var(μ̂) ≤ (b/(b-1))^{s-1} σ²/n` for every measurable `f ∈ L²`, where
`σ² = Var f` and `σ²/n` is the MC variance. -/
theorem variance_scrambledLaw_le (hb : 1 < b) {m s n : ℕ} {d : Fin n → Fin s → Fin D → Fin b}
    (hmD : m ≤ D) (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (hsb : s ≤ b + 1)
    {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s)) :
    Var[fun x ↦ x; scrambledLaw f d] ≤
      ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1) * Var[f; uniformCube s] / n := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hn : n ≠ 0 := by
    rw [hnet.2.1]
    exact (Nat.pow_pos hb0).ne'
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
    have : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    linarith
  have ha : (1 : ℝ) ≤ ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1) := by
    refine one_le_pow₀ ?_
    rw [one_le_div hb1]
    linarith
  rw [variance_scrambledLaw hb hn hfm hf d, variance_eq_cellResVar_add hb0 hf (D := D)]
  set C := ((b : ℝ) / ((b : ℝ) - 1)) ^ (s - 1)
  have hres := cellResVar_nonneg hb0 hf (D := D)
  have hterm : ∀ ℓ ∈ (Finset.univ : Finset (Fin s → Fin (D + 1))).erase 0,
      gainCoeff b d ℓ * haarVar (cellAvg (b := b) f) ℓ ≤ C * haarVar (cellAvg (b := b) f) ℓ := by
    intro ℓ hℓ
    exact mul_le_mul_of_nonneg_right
      (gainCoeff_net_mem_Icc hb hmD hnet hsb (Finset.ne_of_mem_erase hℓ)).2
      (haarVar_nonneg hb0 _ _)
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hsum0 : 0 ≤ ∑ ℓ ∈ (Finset.univ : Finset (Fin s → Fin (D + 1))).erase 0,
      haarVar (cellAvg (b := b) f) ℓ := Finset.sum_nonneg fun ℓ _ ↦ haarVar_nonneg hb0 _ _
  rw [inv_mul_eq_div, div_le_div_iff_of_pos_right hn']
  nlinarith

/-- **The `e` bound** (Owen 1997, `s ≤ b`): `Var(μ̂) ≤ e σ²/n` for scrambled `(0,m,s)`-nets,
whatever the (measurable, square integrable) integrand: scrambled nets never lose more than a
factor `e ≈ 2.718` against Monte Carlo. -/
theorem variance_scrambledLaw_le_exp_one (hb : 1 < b) {m s n : ℕ}
    {d : Fin n → Fin s → Fin D → Fin b} (hmD : m ≤ D)
    (hnet : IsNet b 0 m fun i j ↦ digitPoint (d i j) 0) (hsb : s ≤ b)
    {f : (Fin s → ℝ) → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (uniformCube s)) :
    Var[fun x ↦ x; scrambledLaw f d] ≤ Real.exp 1 * Var[f; uniformCube s] / n := by
  have hb0 : 0 < b := lt_trans Nat.zero_lt_one hb
  have hn : n ≠ 0 := by
    rw [hnet.2.1]
    exact (Nat.pow_pos hb0).ne'
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have := isProbabilityMeasure_uniformCube s
  have hV0 : 0 ≤ Var[f; uniformCube s] := variance_nonneg _ _
  exact (variance_scrambledLaw_le hb hmD hnet (le_trans hsb (Nat.le_succ b)) hfm hf).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_div_sub_one_le_exp_one hb hsb) hV0) hn'.le)

end RQMCMarkov.OwenScrambling
