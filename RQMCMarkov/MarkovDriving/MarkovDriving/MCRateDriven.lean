/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MarkovDriving.MCRate

/-! # The MC rate for the post's MC construction: one i.i.d. sequence driving the chain

Post #3's MC simulation drives the chain by a *single* i.i.d. uniform sequence
(`drivenPath P x₀ u`, `u ∼ iidUniform ℕ`). `MCRate` proves the almost-sure rates for the stack
representation with i.i.d. stacks (`stackPath P x₀ (Function.curry w)`,
`w ∼ iidUniform (Fin n × ℕ)`). This module transfers them.

* `map_drivenPath_eq_map_stackPath_path`: the two **path laws** on `ℕ → Fin n` (product
  σ-algebra) are equal. They agree on every finite-horizon marginal
  (`map_drivenPath_eq_map_stackPath`), hence on all cylinders, and the projective limit of finite
  measures is unique (`IsProjectiveLimit.unique`, cylinders being a generating π-system).
* `ae_drivenPath_of_ae_stackPath`: any **measurable** path event that holds a.s. for the
  i.i.d.-stack path holds a.s. for the driven path. `measurable_occCount_real`,
  `measurable_transCount_real`, `measurable_lilScale_occCount` make the events of `MCRate`
  measurable once their real quantifiers are made countable (`ε = 1/(k+1)`, `K ∈ ℕ`; the
  equivalences are `forall_exists_le_iff_nat`, `exists_le_iff_nat`).
* Transferred results, for `u ∼ iidUniform ℕ`:
  `ae_abs_transCount_driven_le` (upper LIL rate for the transition counts),
  `ae_abs_occCount_driven_le` (occupation error `≤ K + C √(2 T log log T)`),
  `ae_unbounded_occCount_driven` (charged states are visited infinitely often),
  `ae_frequently_transCount_driven_ge` (lower LIL half), `ae_not_tendsto_transCount_driven`,
  and `occupation_error_ranking_driven`, the ranking theorem with MC driving.
-/

namespace RQMCMarkov.MarkovDriving

open MeasureTheory ProbabilityTheory Filter Finset Matrix

variable {n : ℕ}

/-! ### Measurability of path functionals -/

/-- `x ↦ N_i(x, T)` (as a real number) is measurable on the path space. -/
theorem measurable_occCount_real (i : Fin n) (T : ℕ) :
    Measurable fun x : ℕ → Fin n => (occCount x i T : ℝ) := by
  have e : (fun x : ℕ → Fin n => (occCount x i T : ℝ)) =
      fun x => ∑ t ∈ range T, (if x t = i then (1 : ℝ) else 0) :=
    funext fun x => (sum_indicator_eq_occCount x i T).symm
  rw [e]
  exact Finset.measurable_sum _ fun t _ =>
    Measurable.ite (show MeasurableSet {x : ℕ → Fin n | x t = i} from
      (measurable_pi_apply (X := fun _ : ℕ => Fin n) t) (measurableSet_singleton i))
      measurable_const measurable_const

/-- `x ↦ N_ij(x, T)` (as a real number) is measurable on the path space. -/
theorem measurable_transCount_real (i j : Fin n) (T : ℕ) :
    Measurable fun x : ℕ → Fin n => (transCount x i j T : ℝ) := by
  have e : (fun x : ℕ → Fin n => (transCount x i j T : ℝ)) =
      fun x => ∑ t ∈ range T, (if x t = i ∧ x (t + 1) = j then (1 : ℝ) else 0) := by
    funext x
    rw [sum_boole]
    rfl
  rw [e]
  exact Finset.measurable_sum _ fun t _ =>
    Measurable.ite (show MeasurableSet {x : ℕ → Fin n | x t = i ∧ x (t + 1) = j} from
      ((measurable_pi_apply (X := fun _ : ℕ => Fin n) t) (measurableSet_singleton i)).inter
        ((measurable_pi_apply (X := fun _ : ℕ => Fin n) (t + 1))
          (measurableSet_singleton j))) measurable_const
      measurable_const

/-- `x ↦ √(2 N log log N)` with `N = N_i(x, T)` is measurable on the path space. -/
theorem measurable_lilScale_occCount (i : Fin n) (T : ℕ) :
    Measurable fun x : ℕ → Fin n => lilScale (occCount x i T) := by
  have hg : Measurable fun r : ℝ => √(2 * r * Real.log (Real.log r)) := by fun_prop
  exact hg.comp (measurable_occCount_real i T)

/-- A comparison of measurable real functions is a measurable predicate. -/
theorem measurable_le_prop {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => f a ≤ g a :=
  measurableSet_setOfPred.1 (measurableSet_le hf hg)

/-! ### Equality of the path laws -/

/-- The driven path is a measurable map into the path space. -/
theorem measurable_drivenPath (P : Fin n → Fin n → ℝ) (x₀ : Fin n) :
    Measurable (drivenPath P x₀) :=
  measurable_pi_iff.2 fun t =>
    (measurable_pi_apply (⟨t, Nat.lt_succ_self t⟩ : Fin (t + 1))).comp
      (measurable_drivenPath_restrict P x₀ t)

/-- The stack path is a measurable map into the path space. -/
theorem measurable_stackPath (P : Fin n → Fin n → ℝ) (x₀ : Fin n) :
    Measurable fun w : Fin n × ℕ → ℝ => stackPath P x₀ (Function.curry w) :=
  measurable_pi_iff.2 fun t =>
    (measurable_pi_apply (⟨t, Nat.lt_succ_self t⟩ : Fin (t + 1))).comp
      (measurable_stackPath_restrict P x₀ t)

/-- **Equality of the path laws** of MC driving by one i.i.d. sequence and of i.i.d. stacks, as
measures on `ℕ → Fin n`. -/
theorem map_drivenPath_eq_map_stackPath_path {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) : (iidUniform ℕ).map (drivenPath P x₀) =
      (iidUniform (Fin n × ℕ)).map fun w => stackPath P x₀ (Function.curry w) := by
  have := isProbabilityMeasure_iidUniform ℕ
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  set μ := (iidUniform ℕ).map (drivenPath P x₀) with hμ
  set ν := (iidUniform (Fin n × ℕ)).map fun w => stackPath P x₀ (Function.curry w) with hν
  have hμP : IsProjectiveLimit μ fun I => μ.map I.restrict := fun _ => rfl
  refine hμP.unique fun I => ?_
  -- restrict through a finite horizon `T ≥ max I`
  set T := I.sup id
  let ρ : (ℕ → Fin n) → (Fin (T + 1) → Fin n) := fun x t => x t
  let φ : (Fin (T + 1) → Fin n) → (I → Fin n) := fun y i =>
    y ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.2)⟩
  have hρ : Measurable ρ := measurable_pi_iff.2 fun t => measurable_pi_apply _
  have hφ : Measurable φ := measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hres : (I.restrict : (ℕ → Fin n) → (I → Fin n)) = φ ∘ ρ := rfl
  have hd := measurable_drivenPath P x₀
  have hs := measurable_stackPath P x₀
  have key : ν.map ρ = μ.map ρ := by
    rw [hμ, hν, Measure.map_map hρ hd, Measure.map_map hρ hs]
    exact (map_drivenPath_eq_map_stackPath hP x₀ T).symm
  change ν.map I.restrict = μ.map I.restrict
  rw [hres, ← Measure.map_map hφ hρ, ← Measure.map_map hφ hρ, key]

/-- **Transfer**: a measurable path event that holds almost surely for the i.i.d.-stack path holds
almost surely for the path driven by one i.i.d. sequence. -/
theorem ae_drivenPath_of_ae_stackPath {P : Fin n → Fin n → ℝ} (hP : IsStochastic P)
    (x₀ : Fin n) {p : (ℕ → Fin n) → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ w ∂iidUniform (Fin n × ℕ), p (stackPath P x₀ (Function.curry w))) :
    ∀ᵐ u ∂iidUniform ℕ, p (drivenPath P x₀ u) := by
  have h1 : ∀ᵐ x ∂(iidUniform (Fin n × ℕ)).map fun w => stackPath P x₀ (Function.curry w),
      p x := (ae_map_iff (measurable_stackPath P x₀).aemeasurable hp).2 h
  rw [← map_drivenPath_eq_map_stackPath_path hP x₀] at h1
  exact ae_of_ae_map (measurable_drivenPath P x₀).aemeasurable h1

/-! ### Countable reformulations -/

/-- `∀ ε > 0, ∃ K, ∀ T, |e T| ≤ K + (σ + ε) L T` iff the same with `ε = 1/(k+1)`, `K ∈ ℕ`
(for `L ≥ 0`). -/
theorem forall_exists_le_iff_nat {e L : ℕ → ℝ} (hL : ∀ T, 0 ≤ L T) (σ : ℝ) :
    (∀ ε > 0, ∃ K : ℝ, ∀ T, |e T| ≤ K + (σ + ε) * L T) ↔
      ∀ k : ℕ, ∃ K : ℕ, ∀ T, |e T| ≤ K + (σ + 1 / ((k : ℝ) + 1)) * L T := by
  constructor
  · intro h k
    obtain ⟨K, hK⟩ := h (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨⌈K⌉₊, fun T => (hK T).trans (by linarith [Nat.le_ceil K])⟩
  · intro h ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨K, hK⟩ := h k
    refine ⟨K, fun T => (hK T).trans ?_⟩
    have := mul_le_mul_of_nonneg_right (by linarith : σ + 1 / ((k : ℝ) + 1) ≤ σ + ε) (hL T)
    linarith

/-- `∃ K, ∀ T, |e T| ≤ K + c T` iff the same with `K ∈ ℕ`. -/
theorem exists_le_iff_nat {e c : ℕ → ℝ} :
    (∃ K : ℝ, ∀ T, |e T| ≤ K + c T) ↔ ∃ K : ℕ, ∀ T, |e T| ≤ K + c T := by
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨⌈K⌉₊, fun T => (hK T).trans (by linarith [Nat.le_ceil K])⟩
  · rintro ⟨K, hK⟩
    exact ⟨K, hK⟩

variable {P : Fin n → Fin n → ℝ}

/-- The countable form of the upper transition event is measurable. -/
theorem measurableSet_transUpper (i j : Fin n) (σ : ℝ) :
    MeasurableSet {x : ℕ → Fin n | ∀ k : ℕ, ∃ K : ℕ, ∀ T,
      |(transCount x i j T : ℝ) - P i j * occCount x i T| ≤
        K + (σ + 1 / ((k : ℝ) + 1)) * lilScale T} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun k => Measurable.exists fun K =>
    Measurable.forall fun T => measurable_le_prop ?_ measurable_const)
  exact continuous_abs.measurable.comp ((measurable_transCount_real i j T).sub
    ((measurable_occCount_real i T).const_mul (P i j)))

/-- **MC driving, upper LIL rate for the transition counts**: for `u ∼ iidUniform ℕ`, a.s.,
for every `ε > 0` there is `K` with
`|N_ij(T) − p_ij N_i(T)| ≤ K + (√(p_ij (1 − p_ij)) + ε) √(2 T log log T)` for all `T`. -/
theorem ae_abs_transCount_driven_le (hP : IsStochastic P) (x₀ i j : Fin n) :
    ∀ᵐ u ∂iidUniform ℕ, ∀ ε > 0, ∃ K, ∀ T,
      |(transCount (drivenPath P x₀ u) i j T : ℝ) - P i j * occCount (drivenPath P x₀ u) i T|
        ≤ K + (√(P i j * (1 - P i j)) + ε) * lilScale T := by
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  have hst := ae_abs_transCount_mc_le (isIIDStacks_iidUniform (n := n)) hP x₀ i j
  have hdr := ae_drivenPath_of_ae_stackPath hP x₀ (measurableSet_transUpper (P := P) i j
    (√(P i j * (1 - P i j)))) (hst.mono fun w hw =>
      (forall_exists_le_iff_nat (fun T => lilScale_nonneg T) _).1 hw)
  exact hdr.mono fun u hu => (forall_exists_le_iff_nat (fun T => lilScale_nonneg T) _).2 hu

/-- **MC driving, occupation error at the LIL rate**: for `u ∼ iidUniform ℕ`, a.s.
`|N_s(T) − T π_s| ≤ K + C √(2 T log log T)` for all `T`, with `C = Σ_i (σ_i(h) + 1)`. -/
theorem ae_abs_occCount_driven_le (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ}
    {s : Fin n} {μs M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs)
    (hM : ∀ i, |h i| ≤ M) :
    ∀ᵐ u ∂iidUniform ℕ, ∃ K, ∀ T, |(occCount (drivenPath P x₀ u) s T : ℝ) - T * μs| ≤
      K + (∑ i, (√(rowVariance P h i) + 1)) * lilScale T := by
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  set C := ∑ i, (√(rowVariance P h i) + 1)
  have hst := ae_abs_occCount_mc_le (isIIDStacks_iidUniform (n := n)) hP x₀ hh hM
  have hmeas : MeasurableSet {x : ℕ → Fin n | ∃ K : ℕ, ∀ T,
      |(occCount x s T : ℝ) - T * μs| ≤ K + C * lilScale T} := by
    refine measurableSet_setOfPred.2 (Measurable.exists fun K =>
      Measurable.forall fun T => measurable_le_prop ?_ measurable_const)
    exact continuous_abs.measurable.comp ((measurable_occCount_real s T).sub measurable_const)
  have hdr := ae_drivenPath_of_ae_stackPath hP x₀ hmeas
    (hst.mono fun w hw => exists_le_iff_nat.1 hw)
  exact hdr.mono fun u hu => exists_le_iff_nat.2 hu

/-- **MC driving visits every charged state infinitely often** (a.s.). -/
theorem ae_unbounded_occCount_driven (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ}
    {s : Fin n} {μs M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs)
    (hM : ∀ i, |h i| ≤ M) (hμ : 0 < μs) :
    ∀ᵐ u ∂iidUniform ℕ, ∀ v : ℕ, ∃ T, v ≤ occCount (drivenPath P x₀ u) s T := by
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  have hst := ae_tendsto_occCount_mc (isIIDStacks_iidUniform (n := n)) hP x₀ hh hM hμ
  have hmeas : MeasurableSet {x : ℕ → Fin n | ∀ v : ℕ, ∃ T, (v : ℝ) ≤ occCount x s T} :=
    measurableSet_setOfPred.2 (Measurable.forall fun v => Measurable.exists fun T =>
      measurable_le_prop measurable_const (measurable_occCount_real s T))
  have hdr := ae_drivenPath_of_ae_stackPath hP x₀ hmeas
    (hst.mono fun w hw v => (hw v).imp fun T hT => by exact_mod_cast hT)
  exact hdr.mono fun u hu v => (hu v).imp fun T hT => by exact_mod_cast hT

/-- **MC driving, lower LIL half**: if `π_i > 0`, then for `u ∼ iidUniform ℕ`, a.s. for every
`ε > 0`, infinitely often `N_ij(T) − p_ij N_i(T) ≥ (σ − ε) √(2 N log log N)` and infinitely
often `≤ −(σ − ε) √(2 N log log N)`, with `N = N_i(T)`, `σ = √(p_ij (1 − p_ij))`. -/
theorem ae_frequently_transCount_driven_ge (hP : IsStochastic P) (x₀ : Fin n)
    {h : Fin n → ℝ} {i : Fin n} {μi M : ℝ}
    (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - μi) (hM : ∀ k, |h k| ≤ M)
    (hμ : 0 < μi) (j : Fin n) :
    ∀ᵐ u ∂iidUniform ℕ, ∀ ε > 0,
      (∃ᶠ T in atTop, (√(P i j * (1 - P i j)) - ε) *
          lilScale (occCount (drivenPath P x₀ u) i T) ≤
        (transCount (drivenPath P x₀ u) i j T : ℝ) -
          P i j * occCount (drivenPath P x₀ u) i T) ∧
      ∃ᶠ T in atTop, (transCount (drivenPath P x₀ u) i j T : ℝ) -
          P i j * occCount (drivenPath P x₀ u) i T ≤
        -((√(P i j * (1 - P i j)) - ε) * lilScale (occCount (drivenPath P x₀ u) i T)) := by
  have := isProbabilityMeasure_iidUniform (Fin n × ℕ)
  set σ := √(P i j * (1 - P i j))
  -- the countable event
  let E : (ℕ → Fin n) → ℕ → ℝ := fun x T =>
    (transCount x i j T : ℝ) - P i j * occCount x i T
  have hE : ∀ T, Measurable fun x => E x T := fun T =>
    (measurable_transCount_real i j T).sub ((measurable_occCount_real i T).const_mul (P i j))
  have hmeas : MeasurableSet {x : ℕ → Fin n | ∀ k : ℕ,
      (∀ T₀ : ℕ, ∃ T, T₀ ≤ T ∧ (σ - 1 / ((k : ℝ) + 1)) * lilScale (occCount x i T) ≤ E x T) ∧
      ∀ T₀ : ℕ, ∃ T, T₀ ≤ T ∧ E x T ≤ -((σ - 1 / ((k : ℝ) + 1)) *
        lilScale (occCount x i T))} := by
    refine measurableSet_setOfPred.2 (Measurable.forall fun k => Measurable.and
      (Measurable.forall fun T₀ => Measurable.exists fun T => Measurable.and measurable_const
        (measurable_le_prop ((measurable_lilScale_occCount i T).const_mul _) (hE T)))
      (Measurable.forall fun T₀ => Measurable.exists fun T => Measurable.and measurable_const
        (measurable_le_prop (hE T) ((measurable_lilScale_occCount i T).const_mul _).neg)))
  have hst := ae_frequently_transCount_mc_ge (isIIDStacks_iidUniform (n := n)) hP x₀ hh hM hμ j
  have hdr := ae_drivenPath_of_ae_stackPath hP x₀ hmeas (hst.mono fun w hw k => by
    obtain ⟨h1, h2⟩ := hw (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨fun T₀ => (frequently_atTop.1 h1 T₀).imp fun T hT => ⟨hT.1, hT.2⟩,
      fun T₀ => (frequently_atTop.1 h2 T₀).imp fun T hT => ⟨hT.1, hT.2⟩⟩)
  filter_upwards [hdr] with u hu ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨h1, h2⟩ := hu k
  refine ⟨frequently_atTop.2 fun T₀ => (h1 T₀).imp fun T hT => ⟨hT.1, ?_⟩,
    frequently_atTop.2 fun T₀ => (h2 T₀).imp fun T hT => ⟨hT.1, ?_⟩⟩
  · have hL := lilScale_nonneg (occCount (drivenPath P x₀ u) i T)
    have := mul_le_mul_of_nonneg_right (by linarith : σ - ε ≤ σ - 1 / ((k : ℝ) + 1)) hL
    exact this.trans hT.2
  · have hL := lilScale_nonneg (occCount (drivenPath P x₀ u) i T)
    have := mul_le_mul_of_nonneg_right (by linarith : σ - ε ≤ σ - 1 / ((k : ℝ) + 1)) hL
    exact hT.2.trans (by linarith)

/-- **MC driving is not `o(√(N log log N))`-accurate**: for `0 < p_ij < 1` and `π_i > 0`,
for `u ∼ iidUniform ℕ`, almost surely `(N_ij(T) − p_ij N_i(T)) / √(2 N_i(T) log log N_i(T))`
does not tend to `0`. -/
theorem ae_not_tendsto_transCount_driven (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ}
    {i : Fin n} {μi M : ℝ} (hh : ∀ k, h k - (P *ᵥ h) k = (if k = i then 1 else 0) - μi)
    (hM : ∀ k, |h k| ≤ M) (hμ : 0 < μi) {j : Fin n} (hp0 : 0 < P i j) (hp1 : P i j < 1) :
    ∀ᵐ u ∂iidUniform ℕ, ¬ Tendsto (fun T => ((transCount (drivenPath P x₀ u) i j T : ℝ) -
        P i j * occCount (drivenPath P x₀ u) i T) /
          lilScale (occCount (drivenPath P x₀ u) i T)) atTop (nhds 0) := by
  filter_upwards [ae_frequently_transCount_driven_ge hP x₀ hh hM hμ j,
    ae_unbounded_occCount_driven hP x₀ hh hM hμ] with u hω hunb htend
  set x := drivenPath P x₀ u
  set σ := √(P i j * (1 - P i j))
  have hσ : 0 < σ := Real.sqrt_pos.2 (mul_pos hp0 (by linarith))
  obtain ⟨hfr, -⟩ := hω (σ / 2) (by positivity)
  have hsmall := htend.eventually (gt_mem_nhds (show (0 : ℝ) < σ / 2 by positivity))
  have htop : Tendsto (fun T => occCount x i T) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ hab => occCount_mono x i hab) hunb
  have hpos : ∀ᶠ T in atTop, 0 < lilScale (occCount x i T) :=
    (htop.eventually (lil_eventually_le_log 3)).mono fun T hT => lilScale_pos hT
  obtain ⟨T, hT1, hT2, hT3⟩ := (hfr.and_eventually (hsmall.and hpos)).exists
  have h2 := hT2
  rw [div_lt_iff₀ hT3] at h2
  nlinarith

/-- **The ranking theorem for the post's MC construction.** Let `h − Ph = 1_{s} − π_s`,
`|h| ≤ M`. Then:
1. van der Corput stacks: `|N_s(T) − T π_s| ≤ 2M + n V(h) (⌊log₂ T⌋ + 1)` (`O(log T)`);
2. rotors: `|N_s(T) − T π_s| ≤ 2M (1 + Σ_i (L i − 1))` (`O(1)`);
3. MC driving by one i.i.d. uniform sequence: a.s. `|N_s(T) − T π_s| ≤ K + C √(2 T log log T)`
   (`O(√(T log log T))`), and if `π_s > 0` this order is attained for the transition counts
   (`ae_frequently_transCount_driven_ge`). -/
theorem occupation_error_ranking_driven (hP : IsStochastic P) (x₀ : Fin n) {h : Fin n → ℝ}
    {s : Fin n} {μs M : ℝ} (hh : ∀ i, h i - (P *ᵥ h) i = (if i = s then 1 else 0) - μs)
    (hM : ∀ i, |h i| ≤ M) :
    (∀ T, |(occCount (stackPath P x₀ fun _ => vanDerCorput) s T : ℝ) - T * μs| ≤
        2 * M + n * stateVariation h * ((Nat.log 2 T : ℝ) + 1)) ∧
      (∀ (L : Fin n → ℕ) (c : Fin n → ℕ → Fin n), IsRotorCycle P L c → ∀ θ T,
        |(occCount (rotorWalk L c θ x₀) s T : ℝ) - T * μs| ≤
          2 * M * (1 + ∑ i, ((L i - 1 : ℕ) : ℝ))) ∧
      (∀ᵐ u ∂iidUniform ℕ, ∃ K, ∀ T,
        |(occCount (drivenPath P x₀ u) s T : ℝ) - T * μs| ≤
          K + (∑ i, (√(rowVariance P h i) + 1)) * lilScale T) :=
  ⟨fun T => abs_occCount_vdc_sub_le hP x₀ hh hM T,
    fun _ _ hc θ T => abs_occCount_rotorWalk_sub_le hP.nonneg hP.sum_eq_one hc θ x₀ hh hM T,
    ae_abs_occCount_driven_le hP x₀ hh hM⟩

end RQMCMarkov.MarkovDriving
