/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.ChentsovConsistency
import MarkovDriving.ChentsovEntropy

/-! # Chentsov's theorem in general: CUD driving is consistent for every finite chain

Post #3: "if the QMC method we use is 'completely uniformly distributed' … then the generated
Markov simulations are consistent for the empirical state frequencies and time averages
(Chentsov, 1967)". `ChentsovConsistency` proves this under a coupling hypothesis. Here we remove
it: **for every stochastic matrix `P` on a finite state space with a unique stationary
distribution `π`** (e.g. every irreducible `P`, periodic or not), the path driven through the
inverse-CDF update by any CUD sequence has occupation frequencies converging to `π`
(`tendsto_occFreq_of_isCUD_general`) and time averages converging to `π(g)`
(`tendsto_timeAvg_of_isCUD_general`). In particular the chain `fourState`, which has no
coupling box, is consistent (`tendsto_occFreq_fourState_of_isCUD`). Uniqueness of `π` cannot be
dropped (`not_tendsto_occFreq_identity`). The full post #3 claim therefore holds for every
finite chain with a unique stationary distribution.

**Proof.** Write `Z_t = (step P i u_t)ᵢ` for the update map used at time `t` (a finite "cell" of
`u_t`), so `x_{t+1} = Z_t x_t`. For each pattern length `m`, the empirical joint frequencies of
`(x_t, Z_t, …, Z_{t+m-1})` lie in `[0,1]`. If `N_j(T)/T` did not tend to `π_j`, there would be an
ultrafilter `𝒰 ≥ atTop` along which it stays `ε` away; along `𝒰` all these frequencies
converge, to a family `q m` of joint laws. CUD gives that the `Z`-patterns have the i.i.d.
frequencies `∏ c(z_k)` (`isStepFn_pattern`); the time shift `t ↦ t+1` gives exact stationarity;
the marginals are consistent. The entropy lemma `chentsov_entropy_stationary` then shows that
the limit `ρ` of `N(T)/T` along `𝒰` is stationary for `P`, so `ρ = π`, a contradiction.

**Results.**
* `IsSide.inter`, `boxInd_inter`, `IsStepFn.mul`, `isStepFn_finset_prod`: products of step
  functions on the same coordinates are step functions.
* `cellInd`, `cellProb`, `isStepFn_cellInd`, `isStepFn_pattern`, `sum_cellProb_eq`: the cells of
  the inverse-CDF update and their probabilities `∑_{a : a i = j} c a = P i j`.
* `tendsto_occFreq_of_isCUD_general`, `tendsto_timeAvg_of_isCUD_general`: Chentsov's theorem.
* `tendsto_occFreq_fourState_of_isCUD`: the chain without coupling box is consistent.
-/

namespace RQMCMarkov.MarkovDriving

open Filter Topology Finset

/-- The intersection of two sides is a side. -/
theorem IsSide.inter {S S' : Set ℝ} {a b a' b' : ℝ} (h : IsSide S a b) (h' : IsSide S' a' b') :
    IsSide (S ∩ S') (max a a') (max (max a a') (min b b')) := by
  refine ⟨le_max_of_le_left h.1, le_max_left _ _,
    max_le (max_le (h.2.1.trans h.2.2.1) (h'.2.1.trans h'.2.2.1))
      ((min_le_left _ _).trans h.2.2.1), fun y hy => ?_, fun y hy => ?_⟩
  · have h1 : max a a' < y := hy.1
    have h2 : y < max (max a a') (min b b') := hy.2
    have h3 : y < min b b' := by
      rcases lt_max_iff.1 h2 with h4 | h4
      · exact absurd h1 (not_lt.2 h4.le)
      · exact h4
    exact ⟨h.2.2.2.1 ⟨(max_lt_iff.1 h1).1, (lt_min_iff.1 h3).1⟩,
      h'.2.2.2.1 ⟨(max_lt_iff.1 h1).2, (lt_min_iff.1 h3).2⟩⟩
  · have h1 := h.2.2.2.2 ⟨hy.1.1, hy.2⟩
    have h2 := h'.2.2.2.2 ⟨hy.1.2, hy.2⟩
    exact ⟨max_le h1.1 h2.1, (le_min h1.2 h2.2).trans (le_max_right _ _)⟩

/-- The product of two box indicators is the indicator of the intersection. -/
theorem boxInd_inter {d : ℕ} (S S' : Fin d → Set ℝ) (w : Fin d → ℝ) :
    boxInd S w * boxInd S' w = boxInd (fun k => S k ∩ S' k) w := by
  unfold boxInd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Set.inter_indicator_one]
  rfl

/-- **Products of step functions** on the same coordinates are step functions. -/
theorem IsStepFn.mul {d : ℕ} {g h : (Fin d → ℝ) → ℝ} {L M : ℝ} (hg : IsStepFn d g L)
    (hh : IsStepFn d h M) : ∃ K, IsStepFn d (fun w => g w * h w) K := by
  obtain ⟨ι, hι, c, S, a, b, hS, hrep, -⟩ := hg
  obtain ⟨κ, hκ, c', S', a', b', hS', hrep', -⟩ := hh
  refine ⟨_, ι × κ, inferInstance, fun p => c p.1 * c' p.2,
    fun p k => S p.1 k ∩ S' p.2 k, fun p k => max (a p.1 k) (a' p.2 k),
    fun p k => max (max (a p.1 k) (a' p.2 k)) (min (b p.1 k) (b' p.2 k)),
    fun p k => (hS p.1 k).inter (hS' p.2 k), fun w hw => ?_, rfl⟩
  dsimp only
  rw [hrep w hw, hrep' w hw, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  rw [← boxInd_inter]
  ring

/-- Finite products of step functions are step functions. -/
theorem isStepFn_finset_prod {d : ℕ} {α : Type*} (s : Finset α) {g : α → (Fin d → ℝ) → ℝ}
    (h : ∀ i ∈ s, ∃ L, IsStepFn d (g i) L) : ∃ L, IsStepFn d (fun w => ∏ i ∈ s, g i w) L := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, (isStepFn_const d 1).congr fun w _ => (Finset.prod_empty).symm⟩
  | insert i s hi ih =>
    obtain ⟨L, hL⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    obtain ⟨M, hM⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨K, hK⟩ := hM.mul hL
    exact ⟨K, hK.congr fun w _ => (Finset.prod_insert hi (f := fun j => g j w)).symm⟩

/-- Two step-function representations of the same function have the same integral (when some
uniformly distributed sequence exists in that dimension). -/
theorem IsStepFn.unique {d : ℕ} {x : ℕ → Fin d → ℝ} (hx : IsUD x) {g : (Fin d → ℝ) → ℝ}
    {L M : ℝ} (h1 : IsStepFn d g L) (h2 : IsStepFn d g M) : L = M :=
  tendsto_nhds_unique (tendsto_empAvg_of_isStepFn hx h1) (tendsto_empAvg_of_isStepFn hx h2)

variable {n : ℕ}

/-- The **cell** indicator: `1` if the inverse-CDF update map at `v` is `y`, i.e.
`step P i v = y i` for every state `i`. -/
noncomputable def cellInd (P : Fin n → Fin n → ℝ) (y : Fin n → Fin n) (v : ℝ) : ℝ :=
  if (fun i => step P i v) = y then 1 else 0

/-- The cell indicator is the product of the one-state indicators. -/
theorem cellInd_eq_prod (P : Fin n → Fin n → ℝ) (y : Fin n → Fin n) (v : ℝ) :
    cellInd P y v = ∏ i, (if step P i v = y i then (1 : ℝ) else 0) := by
  unfold cellInd
  by_cases h : (fun i => step P i v) = y
  · simp only [h, ↓reduceIte]
    exact (Finset.prod_eq_one fun i _ => by simp only [congrFun h i, ↓reduceIte]).symm
  · simp only [h, ↓reduceIte]
    have : ∃ i, step P i v ≠ y i := by
      by_contra hall
      push Not at hall
      exact h (funext hall)
    obtain ⟨i, hi⟩ := this
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi, ↓reduceIte])).symm

/-- Cells are step functions of one uniform. -/
theorem exists_isStepFn_cellInd {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (y : Fin n → Fin n) : ∃ L, IsStepFn 1 (fun v => cellInd P y (v 0)) L := by
  obtain ⟨L, hL⟩ := isStepFn_finset_prod (d := 1) (Finset.univ : Finset (Fin n))
    (g := fun i v => if step P i (v 0) = y i then (1 : ℝ) else 0)
    fun i _ => ⟨_, isStepFn_step hP i (y i)⟩
  exact ⟨L, hL.congr fun v _ => (cellInd_eq_prod P y (v 0)).symm⟩

/-- The probability of a cell. -/
noncomputable def cellProb {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (y : Fin n → Fin n) :
    ℝ :=
  Classical.choose (exists_isStepFn_cellInd hP y)

/-- The cell indicator is a step function with integral `cellProb`. -/
theorem isStepFn_cellInd {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (y : Fin n → Fin n) :
    IsStepFn 1 (fun v => cellInd P y (v 0)) (cellProb hP y) :=
  Classical.choose_spec (exists_isStepFn_cellInd hP y)

/-- **Patterns of cells** are step functions on windows, with the i.i.d. product
probabilities. -/
theorem isStepFn_pattern {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) (m : ℕ)
    (z : Fin m → Fin n → Fin n) :
    IsStepFn m (fun w => ∏ k, cellInd P (z k) (w k)) (∏ k, cellProb hP (z k)) := by
  induction m with
  | zero =>
    refine ((isStepFn_const 0 1).congr fun w _ => (Fin.prod_univ_zero _).symm).of_eq ?_
    rw [Fin.prod_univ_zero]
  | succ m ih =>
    refine (((ih fun k => z (Fin.castSucc k)).append (isStepFn_cellInd hP (z (Fin.last m)))).congr
      fun w _ => ?_).of_eq ?_
    · rw [Fin.prod_univ_castSucc]
      rfl
    · rw [Fin.prod_univ_castSucc]

/-- The cells refine the inverse-CDF intervals: `∑_{a : a i = j} cellProb a = P i j`. -/
theorem sum_cellProb_eq {P : Fin n → Fin n → ℝ} (hP : IsStochastic P) {x : ℕ → Fin 1 → ℝ}
    (hx : IsUD x) (i j : Fin n) :
    ∑ a : Fin n → Fin n, (if a i = j then cellProb hP a else 0) = P i j := by
  classical
  have h1 : IsStepFn 1 (fun v => ∑ a : Fin n → Fin n, if a i = j then cellInd P a (v 0) else 0)
      (∑ a : Fin n → Fin n, if a i = j then cellProb hP a else 0) := by
    refine isStepFn_finset_sum _ fun a _ => ?_
    by_cases ha : a i = j
    · simp only [ha, ↓reduceIte]
      exact isStepFn_cellInd hP a
    · simp only [ha, ↓reduceIte]
      exact isStepFn_const 1 0
  have h2 := (isStepFn_step hP i j).congr (g' := fun v =>
      ∑ a : Fin n → Fin n, if a i = j then cellInd P a (v 0) else 0) fun v _ => by
    unfold cellInd
    rw [Finset.sum_eq_single (fun k => step P k (v 0))]
    · simp only [↓reduceIte]
    · intro b _ hb
      simp only [Ne.symm hb, ↓reduceIte, ite_self]
    · exact fun h => absurd (Finset.mem_univ _) h
  exact h1.unique hx h2

/-- Sums over all patterns of indicators of a fixed sequence equal `1`. -/
theorem sum_prod_ite_eq_one {C : Type*} [Fintype C] [DecidableEq C] (Z : ℕ → C) (t m : ℕ) :
    ∑ z : Fin m → C, ∏ k : Fin m, (if Z (t + k) = z k then (1 : ℝ) else 0) = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset C))
    fun k y => if Z (t + k) = y then (1 : ℝ) else 0
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  exact Finset.prod_eq_one fun k _ => by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- Limits along an ultrafilter of `[0,1]`-valued sequences exist. -/
theorem exists_tendsto_ultrafilter (𝒰 : Ultrafilter ℕ) {g : ℕ → ℝ}
    (hg : ∀ N, g N ∈ Set.Icc (0 : ℝ) 1) : ∃ a ∈ Set.Icc (0 : ℝ) 1, Tendsto g 𝒰 (𝓝 a) := by
  obtain ⟨a, ha, hle⟩ := isCompact_Icc.ultrafilter_le_nhds (𝒰.map g)
    (by
      rw [Ultrafilter.coe_map, le_principal_iff, Filter.mem_map]
      exact Filter.univ_mem' hg)
  rw [Ultrafilter.coe_map] at hle
  exact ⟨a, ha, hle⟩

/-- An average of `[0,1]`-valued terms lies in `[0,1]`. -/
theorem div_mem_Icc_of_sum {N : ℕ} {g : ℕ → ℝ} (h0 : ∀ t, 0 ≤ g t) (h1 : ∀ t, g t ≤ 1) :
    (∑ t ∈ range N, g t) / N ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (Finset.sum_nonneg fun t _ => h0 t) (Nat.cast_nonneg N), ?_⟩
  rcases Nat.eq_zero_or_pos N with h | h
  · rw [h, Nat.cast_zero, div_zero]
    exact zero_le_one
  · rw [div_le_one (by exact_mod_cast h)]
    calc ∑ t ∈ range N, g t ≤ ∑ t ∈ range N, (1 : ℝ) := Finset.sum_le_sum fun t _ => h1 t
      _ = N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- **Chentsov's theorem, general form** (post #3; Chentsov 1967). Let `P` be a stochastic
matrix on `Fin n` whose stationary distribution `π` is unique, and `u` a CUD sequence. Then for
every start `x₀` the path driven by `u` through the inverse-CDF update has occupation
frequencies `N_j(T)/T → π_j`. No coupling or aperiodicity hypothesis is needed. -/
theorem tendsto_occFreq_of_isCUD_general {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {u : ℕ → ℝ} (hu : IsCUD u) {π : Fin n → ℝ}
    (huniq : ∀ ρ : Fin n → ℝ, (∀ j, ∑ i, ρ i * P i j = ρ j) → (∀ i, 0 ≤ ρ i) →
      ∑ i, ρ i = 1 → ρ = π)
    (x₀ j : Fin n) :
    Tendsto (fun T => (occCount (drivenPath P x₀ u) j T : ℝ) / T) atTop (𝓝 (π j)) := by
  classical
  set x := drivenPath P x₀ u with hx
  set Z : ℕ → Fin n → Fin n := fun t i => step P i (u t) with hZdef
  have hxZ : ∀ t, x (t + 1) = Z t (x t) := fun t => rfl
  -- the empirical quantities
  set e : ℕ → (m : ℕ) → Fin n → (Fin m → Fin n → Fin n) → ℝ := fun N m y z =>
    (∑ t ∈ range N, (if x t = y then (1 : ℝ) else 0) *
      ∏ k : Fin m, (if Z (t + k) = z k then (1 : ℝ) else 0)) / N with he
  set f : ℕ → Fin n → ℝ := fun N y => (occCount x y N : ℝ) / N with hf
  set er : ℕ → Fin n → (Fin n → Fin n) → ℝ := fun N y a =>
    (∑ t ∈ range N, (if x t = y then (1 : ℝ) else 0) * (if Z t = a then (1 : ℝ) else 0)) / N
    with her
  have hind01 : ∀ (p : Prop) [Decidable p], (0 : ℝ) ≤ (if p then 1 else 0) ∧
      (if p then (1 : ℝ) else 0) ≤ 1 := fun p _ => by
    split_ifs
    · exact ⟨zero_le_one, le_refl 1⟩
    · exact ⟨le_refl 0, zero_le_one⟩
  have hprod01 : ∀ (t m : ℕ) (z : Fin m → Fin n → Fin n),
      0 ≤ ∏ k : Fin m, (if Z (t + k) = z k then (1 : ℝ) else 0) ∧
        ∏ k : Fin m, (if Z (t + k) = z k then (1 : ℝ) else 0) ≤ 1 := fun t m z =>
    ⟨Finset.prod_nonneg fun k _ => (hind01 _).1,
      Finset.prod_le_one₀ (fun k _ => (hind01 _).1) fun k _ => (hind01 _).2⟩
  have he01 : ∀ N m y z, e N m y z ∈ Set.Icc (0 : ℝ) 1 := fun N m y z =>
    div_mem_Icc_of_sum (fun t => mul_nonneg (hind01 _).1 (hprod01 t m z).1)
      fun t => (mul_le_of_le_one_left (hprod01 t m z).1 (hind01 _).2).trans (hprod01 t m z).2
  have hf01 : ∀ N y, f N y ∈ Set.Icc (0 : ℝ) 1 := fun N y => by
    rw [hf]
    dsimp only
    rw [occCount_eq_sum]
    exact div_mem_Icc_of_sum (fun t => (hind01 _).1) fun t => (hind01 _).2
  have her01 : ∀ N y a, er N y a ∈ Set.Icc (0 : ℝ) 1 := fun N y a =>
    div_mem_Icc_of_sum (fun t => mul_nonneg (hind01 _).1 (hind01 _).1)
      fun t => (mul_le_of_le_one_left (hind01 _).1 (hind01 _).2).trans (hind01 _).2
  -- exact identities at finite `N`
  have hXN : ∀ N m y, ∑ z, e N m y z = f N y := by
    intro N m y
    rw [he, hf]
    dsimp only
    rw [← Finset.sum_div, Finset.sum_comm, occCount_eq_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum, sum_prod_ite_eq_one Z t m, mul_one]
  have hsplit : ∀ (t L : ℕ) (a : Fin n → Fin n) (z' : Fin L → Fin n → Fin n),
      ∏ k : Fin (L + 1), (if Z (t + k) = (Fin.cons a z' : Fin (L + 1) → Fin n → Fin n) k
        then (1 : ℝ) else 0) =
      (if Z t = a then (1 : ℝ) else 0) *
        ∏ k : Fin L, (if Z (t + 1 + k) = z' k then (1 : ℝ) else 0) := by
    intro t L a z'
    rw [Fin.prod_univ_succ]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Fin.cons_succ, Fin.val_succ, show t + (k + 1) = t + 1 + k by omega]
  have hrN : ∀ N L y a, ∑ z', e N (L + 1) y (Fin.cons a z') = er N y a := by
    intro N L y a
    rw [he, her]
    dsimp only
    rw [← Finset.sum_div, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hsplit]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_prod_ite_eq_one Z (t + 1) L, mul_one]
  have hstatN : ∀ N L j z', 0 < N → |∑ y, ∑ a, (if a y = j then e N (L + 1) y (Fin.cons a z')
      else 0) - e N L j z'| ≤ 1 / N := by
    intro N L j z' hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    set g : ℕ → ℝ := fun t => (if x t = j then (1 : ℝ) else 0) *
      ∏ k : Fin L, (if Z (t + k) = z' k then (1 : ℝ) else 0) with hg
    have step1 : ∀ y a, (if a y = j then e N (L + 1) y (Fin.cons a z') else 0) =
        (∑ t ∈ range N, (if a y = j then (if x t = y then (1 : ℝ) else 0) *
          ((if Z t = a then (1 : ℝ) else 0) *
            ∏ k : Fin L, (if Z (t + 1 + k) = z' k then (1 : ℝ) else 0)) else 0)) / N := by
      intro y a
      rw [he]
      dsimp only
      by_cases h : a y = j
      · simp only [h, ↓reduceIte, hsplit]
      · simp only [h, ↓reduceIte, Finset.sum_const_zero, zero_div]
    have hlhs : ∑ y, ∑ a, (if a y = j then e N (L + 1) y (Fin.cons a z') else 0) =
        (∑ t ∈ range N, g (t + 1)) / N := by
      simp only [step1]
      simp only [← Finset.sum_div]
      congr 1
      refine (Finset.sum_congr rfl fun y _ => Finset.sum_comm).trans ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_eq_single (x t)]
      · rw [Finset.sum_eq_single (Z t)]
        · rw [hg]
          dsimp only
          rw [hxZ]
          by_cases h : Z t (x t) = j
          · simp only [h, ↓reduceIte, one_mul]
          · simp only [h, ↓reduceIte]
            ring
        · intro a _ ha
          by_cases h : a (x t) = j
          · simp only [h, ↓reduceIte, Ne.symm ha, zero_mul, mul_zero]
          · simp only [h, ↓reduceIte]
        · exact fun h => absurd (Finset.mem_univ _) h
      · intro y _ hy
        refine Finset.sum_eq_zero fun a _ => ?_
        by_cases h : a y = j
        · simp only [h, ↓reduceIte, Ne.symm hy, zero_mul]
        · simp only [h, ↓reduceIte]
      · exact fun h => absurd (Finset.mem_univ _) h
    have hrhs : e N L j z' = (∑ t ∈ range N, g t) / N := rfl
    rw [hlhs, hrhs, ← sub_div, abs_div, abs_of_pos hNR]
    refine div_le_div_of_nonneg_right ?_ hNR.le
    have h1 := Finset.sum_range_succ' g N
    have h2 := Finset.sum_range_succ g N
    have hgN : 0 ≤ g N ∧ g N ≤ 1 := ⟨mul_nonneg (hind01 _).1 (hprod01 N L z').1,
      (mul_le_of_le_one_left (hprod01 N L z').1 (hind01 _).2).trans (hprod01 N L z').2⟩
    have hg0 : 0 ≤ g 0 ∧ g 0 ≤ 1 := ⟨mul_nonneg (hind01 _).1 (hprod01 0 L z').1,
      (mul_le_of_le_one_left (hprod01 0 L z').1 (hind01 _).2).trans (hprod01 0 L z').2⟩
    rw [abs_le]
    constructor <;> linarith
  -- the bad event
  by_contra hnot
  obtain ⟨ε, hε, hfr⟩ : ∃ ε > 0, ∃ᶠ N in atTop, ε ≤ |f N j - π j| := by
    rw [Metric.tendsto_atTop] at hnot
    push Not at hnot
    obtain ⟨ε, hε, h⟩ := hnot
    refine ⟨ε, hε, Filter.frequently_atTop.2 fun N0 => ?_⟩
    obtain ⟨N, hN, hd⟩ := h N0
    exact ⟨N, hN, by rwa [Real.dist_eq] at hd⟩
  have hne := Filter.frequently_iff_neBot.1 hfr
  set 𝒰 : Ultrafilter ℕ := Ultrafilter.of (atTop ⊓ 𝓟 {N | ε ≤ |f N j - π j|}) with h𝒰
  have h𝒰le : (𝒰 : Filter ℕ) ≤ atTop ⊓ 𝓟 {N | ε ≤ |f N j - π j|} := Ultrafilter.of_le _
  have h𝒰top : (𝒰 : Filter ℕ) ≤ atTop := h𝒰le.trans inf_le_left
  have h𝒰bad : ∀ᶠ N in (𝒰 : Filter ℕ), ε ≤ |f N j - π j| :=
    le_principal_iff.1 (h𝒰le.trans inf_le_right)
  -- limits along the ultrafilter
  choose q hq01 hq using fun m y z => exists_tendsto_ultrafilter 𝒰 fun N => he01 N m y z
  choose ρ hρ01 hρ using fun y => exists_tendsto_ultrafilter 𝒰 fun N => hf01 N y
  choose r hr01 hrlim using fun y a => exists_tendsto_ultrafilter 𝒰 fun N => her01 N y a
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / N) (𝒰 : Filter ℕ) (𝓝 0) :=
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).mono_left h𝒰top
  have hpos : ∀ᶠ N in (𝒰 : Filter ℕ), 0 < N := h𝒰top (eventually_gt_atTop 0)
  -- the hypotheses of the entropy lemma
  have hZ' : ∀ m z, ∑ y, q m y z = ∏ k, cellProb hP (z k) := by
    intro m z
    refine tendsto_nhds_unique (tendsto_finsetSum _ fun y _ => hq m y z) ?_
    have hpat := (tendsto_empAvg_of_isStepFn (hu m) (isStepFn_pattern hP m z)).mono_left h𝒰top
    refine hpat.congr fun N => ?_
    rw [he]
    dsimp only
    rw [← Finset.sum_div, Finset.sum_comm]
    unfold empAvg
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, one_mul]
    rfl
  have hX' : ∀ m y, ∑ z, q m y z = ρ y := fun m y =>
    tendsto_nhds_unique (tendsto_finsetSum _ fun z _ => hq m y z)
      ((hρ y).congr fun N => (hXN N m y).symm)
  have hr' : ∀ L y a, ∑ z', q (L + 1) y (Fin.cons a z') = r y a := fun L y a =>
    tendsto_nhds_unique (tendsto_finsetSum _ fun z' _ => hq (L + 1) y _)
      ((hrlim y a).congr fun N => (hrN N L y a).symm)
  have hstat' : ∀ L j' z', ∑ y, ∑ a, (if a y = j' then q (L + 1) y (Fin.cons a z') else 0) =
      q L j' z' := by
    intro L j' z'
    have h1 : Tendsto (fun N => ∑ y, ∑ a, (if a y = j' then e N (L + 1) y (Fin.cons a z')
        else 0)) (𝒰 : Filter ℕ)
        (𝓝 (∑ y, ∑ a, (if a y = j' then q (L + 1) y (Fin.cons a z') else 0))) :=
      tendsto_finsetSum _ fun y _ => tendsto_finsetSum _ fun a _ => by
        by_cases h : a y = j'
        · simp only [h, ↓reduceIte]
          exact hq _ _ _
        · simp only [h, ↓reduceIte]
          exact tendsto_const_nhds
    have h2 : Tendsto (fun N => ∑ y, ∑ a, (if a y = j' then e N (L + 1) y (Fin.cons a z')
        else 0)) (𝒰 : Filter ℕ) (𝓝 (q L j' z')) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h3 := hinv.add (tendsto_iff_norm_sub_tendsto_zero.1 (hq L j' z'))
      rw [add_zero] at h3
      refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ h3
      filter_upwards [hpos] with N hN
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      calc _ ≤ |∑ y, ∑ a, (if a y = j' then e N (L + 1) y (Fin.cons a z') else 0) -
            e N L j' z'| + |e N L j' z' - q L j' z'| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add_left (hstatN N L j' z' hN) _
    exact tendsto_nhds_unique h1 h2
  have hρ1 : ∑ y, ρ y = 1 := by
    refine tendsto_nhds_unique (tendsto_finsetSum _ fun y _ => hρ y)
      (tendsto_const_nhds.congr' ?_)
    filter_upwards [hpos] with N hN
    rw [hf]
    dsimp only
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_occCount, div_self (by exact_mod_cast hN.ne')]
  have hstatρ := chentsov_entropy_stationary (X := Fin n) (C := Fin n → Fin n)
    (fun y a => a y) (cellProb hP) ρ r q (fun m y z => (hq01 m y z).1) hZ' hX' hr' hstat' hρ1
  have hρP : ∀ j', ∑ i, ρ i * P i j' = ρ j' := fun j' => by
    rw [← hstatρ j']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_cellProb_eq hP (hu 1) i j']
  have hρπ := huniq ρ hρP (fun i => (hρ01 i).1) hρ1
  have hlimj := hρ j
  rw [hρπ] at hlimj
  obtain ⟨N, hN1, hN2⟩ := ((Metric.tendsto_nhds.1 hlimj ε hε).and h𝒰bad).exists
  rw [Real.dist_eq] at hN1
  linarith

/-- **Time averages, general form** (post #3): under the hypotheses of
`tendsto_occFreq_of_isCUD_general`, `(1/T) ∑_{t<T} g(x_t) → ∑_j π_j g(j)`. -/
theorem tendsto_timeAvg_of_isCUD_general {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    {u : ℕ → ℝ} (hu : IsCUD u) {π : Fin n → ℝ}
    (huniq : ∀ ρ : Fin n → ℝ, (∀ j, ∑ i, ρ i * P i j = ρ j) → (∀ i, 0 ≤ ρ i) →
      ∑ i, ρ i = 1 → ρ = π)
    (x₀ : Fin n) (g : Fin n → ℝ) :
    Tendsto (fun T => (∑ t ∈ range T, g (drivenPath P x₀ u t)) / T) atTop
      (𝓝 (∑ j, π j * g j)) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun j _ =>
    (tendsto_occFreq_of_isCUD_general hP hu huniq x₀ j).mul_const (g j)
  refine h.congr fun T => ?_
  have hfib : ∀ t, g (drivenPath P x₀ u t) =
      ∑ j, (if drivenPath P x₀ u t = j then (1 : ℝ) else 0) * g j := fun t => by
    rw [Finset.sum_eq_single (drivenPath P x₀ u t)
      (fun k _ hk => by simp only [Ne.symm hk, ↓reduceIte, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [↓reduceIte, one_mul]
  rw [Finset.sum_congr rfl fun t _ => hfib t, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [occCount_eq_sum, ← Finset.sum_mul, div_mul_eq_mul_div]

/-- **The chain without a coupling box is consistent.** For `fourState` (no coupling box of
any length, `not_hasCouplingBox_fourState`) and every CUD driving sequence, every state has
limiting frequency `1/4`. -/
theorem tendsto_occFreq_fourState_of_isCUD {u : ℕ → ℝ} (hu : IsCUD u) (x₀ j : Fin 4) :
    Tendsto (fun T => (occCount (drivenPath fourState x₀ u) j T : ℝ) / T) atTop
      (𝓝 (1 / 4)) := by
  refine tendsto_occFreq_of_isCUD_general (π := fun _ => 1 / 4) isStochastic_fourState hu
    (fun ρ hρ _ hρ1 => funext fun j' => ?_) x₀ j
  rw [← sum_mul_multiStep hρ 2 j']
  simp only [multiStep_fourState_two]
  rw [← Finset.sum_mul, hρ1, one_mul]

end RQMCMarkov.MarkovDriving
