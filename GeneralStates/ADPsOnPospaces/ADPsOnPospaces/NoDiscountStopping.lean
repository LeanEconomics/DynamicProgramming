/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPsOnPospaces.MinPospace
import ADPsOnPospaces.BoundedMeasurable
import ADPsOnPospaces.MarkovOperator

/-!
# No-discount optimal stopping

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §3.2.3 (pp. 110–116).

A controller watching a `P`-Markov state decides when to stop: stopping in state `x` costs
`e(x)`, continuing costs `c(x)`, with `e, c ∈ bX₊` and no discounting. A policy is a measurable
exit region `E` containing the certain exit region `Ē = {e ≤ c}` (3.14), (3.16). With
`K_E g = 𝟙_{Eᶜ} Pg` (3.20) the policy operator is `T_E g = 𝟙_E e + 𝟙_{Eᶜ}(c + Pg)` (3.18)–(3.19).

The probabilistic objects are expressed through these operators: `ℙ_x{τ_E ≥ n} = (K_Eⁿ𝟙)(x)` (the
computation in the proof of Lemma 3.2.6), so `𝔼_x τ̄ = ∑_{n ≥ 1} (K_Ēⁿ𝟙)(x)`, and the `σ`-loss
function (3.13) is `g_E = ∑ₜ K_Eᵗ h_E` with `h_E = 𝟙_E e + 𝟙_{Eᶜ} c`. Identifying these with the
path-space expectations is the Markov property, not formalised here.

* **Exercise A.2.1**: an asymptotically contracting map with a fixed point is globally stable.
* **Assumption 3.2.1**: `sup_x 𝔼_x τ̄ < ∞`.
* **Lemma 3.2.3**: `g_E` is finite and bounded; **Lemma 3.2.4**: `T_E g_E = g_E`.
* **Lemma 3.2.6** (`‖K_Eⁿ f‖ ≤ ‖f‖ sup_x ℙ_x{τ_E ≥ n}`), **Lemma 3.2.7**
  (`sup_x ℙ_x{τ_E ≥ n} → 0`), **Lemma 3.2.8** (asymptotic contraction) and **Proposition 3.2.5**
  (global stability on `bX₊`).
* The ADP `(bX₊, 𝕋)` is min-regular (§3.2.3.5) and its Bellman min-equation is (3.11).
* **Theorem 3.2.9**: the fundamental min-optimality properties hold, and min-VFI, min-OPI and
  min-HPI all converge (via Theorem 3.1.8).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ADPsOnPospaces

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace

/-- **Exercise A.2.1** (p. 346): an asymptotically contracting self-map with a fixed point is
globally stable. -/
theorem exercise_A_2_1 {V : Type*} [MetricSpace V] {S : V → V}
    (hS : ∀ u v, Tendsto (fun n => dist (S^[n] u) (S^[n] v)) atTop (𝓝 0)) {vbar : V}
    (hfix : S vbar = vbar) : GloballyStable S := by
  have hit : ∀ n, S^[n] vbar = vbar := fun n => iterate_fixed hfix n
  refine ⟨vbar, hfix, fun w hw => ?_, fun u => ?_⟩
  · have h := hS w vbar
    simp only [iterate_fixed hw, hit] at h
    exact dist_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds h)
  · refine tendsto_iff_dist_tendsto_zero.2 ?_
    simpa only [hit] using hS u vbar

/-- The no-discount optimal stopping problem (§3.2.3.1): a stochastic kernel `P`, an exit cost
`e ∈ bX₊` and a flow cost `c ∈ bX₊`. -/
structure NoDiscountStopping (X : Type*) [MeasurableSpace X] where
  /-- the transition kernel -/
  P : Kernel X X
  /-- the exit cost -/
  e : BM X
  e_nonneg : 0 ≤ e
  /-- the flow cost -/
  c : BM X
  c_nonneg : 0 ≤ c

namespace NoDiscountStopping

variable {X : Type*} [MeasurableSpace X] (M : NoDiscountStopping X)

/-- The certain exit region `Ē = {e ≤ c}` (3.14). -/
def Ebar : Set X := {x | M.e.toFun x ≤ M.c.toFun x}

theorem measurableSet_Ebar : MeasurableSet M.Ebar :=
  measurableSet_le M.e.measurable' M.c.measurable'

/-- Policies (3.16): measurable exit regions `E ⊇ Ē` (the indicator of `E` is `σ ≥ σ̄`). -/
def Policy : Type _ := {E : Set X // MeasurableSet E ∧ M.Ebar ⊆ E}

/-- The lower bound policy `σ̄ = 𝟙{e ≤ c}`. -/
def barPolicy : M.Policy := ⟨M.Ebar, M.measurableSet_Ebar, subset_rfl⟩

variable [IsMarkovKernel M.P]

/-- The Markov operator `P` on `bX`. -/
noncomputable def Pop (g : BM X) : BM X :=
  ⟨markovOp M.P g.toFun, measurable_markovOp M.P g.measurable',
    ⟨‖g‖, abs_markovOp_le M.P (BM.abs_le_norm g)⟩⟩

/-- `K_E g = 𝟙_{Eᶜ} Pg` (3.20). -/
noncomputable def K (σ : M.Policy) (g : BM X) : BM X :=
  ⟨σ.1ᶜ.indicator (markovOp M.P g.toFun),
    (measurable_markovOp M.P g.measurable').indicator σ.2.1.compl,
    ⟨‖g‖, fun x => by
      by_cases hx : x ∈ σ.1ᶜ
      · rw [indicator_of_mem hx]
        exact abs_markovOp_le M.P (BM.abs_le_norm g) x
      · rw [indicator_of_notMem hx, abs_zero]
        exact norm_nonneg g⟩⟩

/-- The one-period cost `h_E = 𝟙_E e + 𝟙_{Eᶜ} c`. -/
noncomputable def hcost (σ : M.Policy) : BM X :=
  ⟨fun x => σ.1.indicator M.e.toFun x + σ.1ᶜ.indicator M.c.toFun x,
    (M.e.measurable'.indicator σ.2.1).add (M.c.measurable'.indicator σ.2.1.compl),
    ⟨‖M.e‖ + ‖M.c‖, fun x => by
      by_cases hx : x ∈ σ.1
      · rw [indicator_of_mem hx, indicator_of_notMem (notMem_compl_iff.2 hx), add_zero]
        exact (BM.abs_le_norm _ x).trans (le_add_of_nonneg_right (norm_nonneg _))
      · rw [indicator_of_notMem hx, indicator_of_mem (mem_compl hx), zero_add]
        exact (BM.abs_le_norm _ x).trans (le_add_of_nonneg_left (norm_nonneg _))⟩⟩

/-- The policy operator (3.19): `T_E g = h_E + K_E g`. -/
noncomputable def T (σ : M.Policy) (g : BM X) : BM X := M.hcost σ + M.K σ g

theorem K_apply_mem {σ : M.Policy} {x : X} (hx : x ∈ σ.1) (g : BM X) :
    (M.K σ g).toFun x = 0 :=
  indicator_of_notMem (notMem_compl_iff.2 hx) _

theorem K_apply_notMem {σ : M.Policy} {x : X} (hx : x ∉ σ.1) (g : BM X) :
    (M.K σ g).toFun x = markovOp M.P g.toFun x :=
  indicator_of_mem (mem_compl hx) _

/-- (3.18): `(T_E g)(x) = e(x)` on `E` and `c(x) + (Pg)(x)` off `E`. -/
theorem T_apply_mem {σ : M.Policy} {x : X} (hx : x ∈ σ.1) (g : BM X) :
    (M.T σ g).toFun x = M.e.toFun x := by
  simp only [T, BM.add_apply, hcost, M.K_apply_mem hx, indicator_of_mem hx,
    indicator_of_notMem (notMem_compl_iff.2 hx), add_zero]

theorem T_apply_notMem {σ : M.Policy} {x : X} (hx : x ∉ σ.1) (g : BM X) :
    (M.T σ g).toFun x = M.c.toFun x + markovOp M.P g.toFun x := by
  simp only [T, BM.add_apply, hcost, M.K_apply_notMem hx, indicator_of_notMem hx,
    indicator_of_mem (mem_compl hx), zero_add]

/-! ### Linearity and positivity of `K_E` -/

theorem K_add (σ : M.Policy) (f g : BM X) : M.K σ (f + g) = M.K σ f + M.K σ g :=
  BM.ext fun x => by
    have h := congrFun (markovOp_add M.P (BM.mem_bX f) (BM.mem_bX g)) x
    simp only [K, BM.add_apply]
    by_cases hx : x ∈ σ.1ᶜ
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
      exact h
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, add_zero]

theorem K_smul (σ : M.Policy) (a : ℝ) (f : BM X) : M.K σ (a • f) = a • M.K σ f :=
  BM.ext fun x => by
    simp only [K, BM.smul_apply]
    have := markovOp_smul M.P a f.toFun
    by_cases hx : x ∈ σ.1ᶜ
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      exact congrFun this x
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]

theorem K_sub (σ : M.Policy) (f g : BM X) : M.K σ (f - g) = M.K σ f - M.K σ g :=
  BM.ext fun x => by
    have h := congrFun (markovOp_sub M.P (BM.mem_bX f) (BM.mem_bX g)) x
    simp only [K, BM.sub_apply]
    by_cases hx : x ∈ σ.1ᶜ
    · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
      exact h
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, sub_zero]

theorem K_mono (σ : M.Policy) {f g : BM X} (h : f ≤ g) : M.K σ f ≤ M.K σ g := fun x => by
  by_cases hx : x ∈ σ.1
  · rw [M.K_apply_mem hx, M.K_apply_mem hx]
  · rw [M.K_apply_notMem hx, M.K_apply_notMem hx]
    exact markovOp_mono M.P (BM.mem_bX f) (BM.mem_bX g) h x

theorem K_nonneg (σ : M.Policy) {f : BM X} (h : 0 ≤ f) : 0 ≤ M.K σ f := by
  have := M.K_mono σ h
  rwa [show M.K σ 0 = 0 from by simpa using M.K_smul σ 0 0] at this

theorem K_const_le (σ : M.Policy) {a : ℝ} (ha : 0 ≤ a) : M.K σ (BM.const a) ≤ BM.const a :=
  fun x => by
    by_cases hx : x ∈ σ.1
    · rw [M.K_apply_mem hx]
      exact ha
    · rw [M.K_apply_notMem hx]
      exact (congrFun (markovOp_const M.P a) x).le

/-- A larger exit region discounts less: `K_E f ≤ K_F f` for `f ≥ 0` and `F ⊆ E`. -/
theorem K_le_of_subset {σ τ : M.Policy} (hst : τ.1 ⊆ σ.1) {f : BM X} (hf : 0 ≤ f) :
    M.K σ f ≤ M.K τ f := fun x => by
  by_cases hx : x ∈ σ.1
  · rw [M.K_apply_mem hx]
    exact M.K_nonneg τ hf x
  · rw [M.K_apply_notMem hx, M.K_apply_notMem (fun h => hx (hst h))]

theorem iterate_K_mono (σ : M.Policy) (n : ℕ) : Monotone (M.K σ)^[n] :=
  Monotone.iterate (fun _ _ h => M.K_mono σ h) n

theorem iterate_K_nonneg (σ : M.Policy) (n : ℕ) {f : BM X} (h : 0 ≤ f) :
    0 ≤ (M.K σ)^[n] f := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [iterate_succ_apply']
    exact M.K_nonneg σ ih

theorem iterate_K_smul (σ : M.Policy) (n : ℕ) (a : ℝ) (f : BM X) :
    (M.K σ)^[n] (a • f) = a • (M.K σ)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ih, M.K_smul]

theorem iterate_K_sub (σ : M.Policy) (n : ℕ) (f g : BM X) :
    (M.K σ)^[n] (f - g) = (M.K σ)^[n] f - (M.K σ)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply', ih, M.K_sub]

/-! ### Survival probabilities -/

/-- `ℙ_x{τ_E ≥ n} = (K_Eⁿ𝟙)(x)`. -/
noncomputable def surv (σ : M.Policy) (n : ℕ) : BM X := (M.K σ)^[n] (BM.const 1)

theorem surv_nonneg (σ : M.Policy) (n : ℕ) : 0 ≤ M.surv σ n :=
  M.iterate_K_nonneg σ n fun _ => zero_le_one

theorem surv_succ_le (σ : M.Policy) (n : ℕ) : M.surv σ (n + 1) ≤ M.surv σ n := by
  simp only [surv]
  rw [iterate_succ_apply]
  exact M.iterate_K_mono σ n (M.K_const_le σ zero_le_one)

theorem surv_anti (σ : M.Policy) : Antitone (M.surv σ) :=
  antitone_nat_of_succ_le (M.surv_succ_le σ)

/-- (3.17): every policy stops no later than the upper bound stopping time `τ̄`. -/
theorem surv_le_surv_bar (σ : M.Policy) (n : ℕ) : M.surv σ n ≤ M.surv M.barPolicy n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [surv] at ih ⊢
    rw [iterate_succ_apply', iterate_succ_apply']
    exact (M.K_le_of_subset σ.2.2 (M.iterate_K_nonneg σ n fun _ => zero_le_one)).trans
      (M.K_mono _ ih)

/-- **Lemma 3.2.6** (p. 114), pointwise: `|(K_Eⁿ f)(x)| ≤ ‖f‖ ℙ_x{τ_E ≥ n}`. -/
theorem abs_iterate_K_le (σ : M.Policy) (n : ℕ) (f : BM X) (x : X) :
    |((M.K σ)^[n] f).toFun x| ≤ ‖f‖ * (M.surv σ n).toFun x := by
  have hup : f ≤ ‖f‖ • BM.const 1 := fun y => by
    simpa using (le_abs_self _).trans (BM.abs_le_norm f y)
  have hlo : -‖f‖ • BM.const 1 ≤ f := fun y => by
    simpa using neg_le_of_abs_le (BM.abs_le_norm f y)
  have h1 := M.iterate_K_mono σ n hup x
  have h2 := M.iterate_K_mono σ n hlo x
  rw [M.iterate_K_smul] at h1 h2
  simp only [BM.smul_apply] at h1 h2
  exact abs_le.2 ⟨by simpa [surv] using h2, by simpa [surv] using h1⟩

/-- **Lemma 3.2.6** (p. 114): `‖K_Eⁿ f‖ ≤ ‖f‖ · sup_x ℙ_x{τ_E ≥ n}`. -/
theorem lemma_3_2_6 (σ : M.Policy) (n : ℕ) (f : BM X) :
    ‖(M.K σ)^[n] f‖ ≤ ‖f‖ * ‖M.surv σ n‖ :=
  BM.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun x =>
    (M.abs_iterate_K_le σ n f x).trans (mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (BM.abs_le_norm _ x)) (norm_nonneg _))

/-- **Assumption 3.2.1** (p. 112): `sup_x 𝔼_x τ̄ < ∞`, with
`𝔼_x τ̄ = ∑_{n ≥ 1} ℙ_x{τ̄ ≥ n} = ∑_{n ≥ 1} (K_Ēⁿ𝟙)(x)`. -/
def Assumption321 : Prop :=
  ∃ C, ∀ N x, ∑ n ∈ Finset.range N, (M.surv M.barPolicy (n + 1)).toFun x ≤ C

/-- **Lemma 3.2.7** (p. 115): under Assumption 3.2.1, `sup_x ℙ_x{τ_E ≥ n} → 0` for every policy. -/
theorem lemma_3_2_7 (hA : M.Assumption321) (σ : M.Policy) :
    Tendsto (fun n => ‖M.surv σ n‖) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hA
  set C' := max C 0
  have hbound : ∀ n, 1 ≤ n → ‖M.surv σ n‖ ≤ C' / n := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine BM.norm_le (div_nonneg (le_max_right _ _) hn'.le) fun x => ?_
    rw [abs_of_nonneg (M.surv_nonneg σ n x), le_div_iff₀ hn']
    have hsum : (n : ℝ) * (M.surv M.barPolicy n).toFun x ≤
        ∑ k ∈ Finset.range n, (M.surv M.barPolicy (k + 1)).toFun x := by
      have : ∀ k ∈ Finset.range n, (M.surv M.barPolicy n).toFun x ≤
          (M.surv M.barPolicy (k + 1)).toFun x := fun k hk =>
        M.surv_anti M.barPolicy (Finset.mem_range.1 hk) x
      simpa using Finset.card_nsmul_le_sum _ _ _ this
    calc (M.surv σ n).toFun x * n ≤ (M.surv M.barPolicy n).toFun x * n :=
          mul_le_mul_of_nonneg_right (M.surv_le_surv_bar σ n x) hn'.le
      _ ≤ C' := by linarith [hC n x, le_max_left C 0]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_atTop.2 ⟨1, hbound⟩) ?_
  simpa using tendsto_const_div_atTop_nhds_zero_nat C'

/-- `T_E f − T_E g = K_E(f − g)`, so `T_Eⁿ f − T_Eⁿ g = K_Eⁿ(f − g)`. -/
theorem iterate_T_sub (σ : M.Policy) (n : ℕ) (f g : BM X) :
    (M.T σ)^[n] f - (M.T σ)^[n] g = (M.K σ)^[n] (f - g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', iterate_succ_apply', ← ih, M.K_sub]
    simp only [T]
    abel

/-- **Lemma 3.2.8** (p. 116): under Assumption 3.2.1 each `T_E` is asymptotically contracting:
`‖T_Eⁿ f − T_Eⁿ g‖ ≤ ‖f − g‖ sup_x ℙ_x{τ_E ≥ n} → 0`. -/
theorem lemma_3_2_8 (hA : M.Assumption321) (σ : M.Policy) (f g : BM X) :
    Tendsto (fun n => dist ((M.T σ)^[n] f) ((M.T σ)^[n] g)) atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (by simpa using (M.lemma_3_2_7 hA σ).const_mul ‖f - g‖)
  rw [dist_eq_norm, M.iterate_T_sub]
  exact M.lemma_3_2_6 σ n (f - g)

theorem K_zero (σ : M.Policy) : M.K σ 0 = 0 := by simpa using M.K_smul σ 0 0

theorem K_sum (σ : M.Policy) (s : Finset ℕ) (f : ℕ → BM X) :
    M.K σ (∑ t ∈ s, f t) = ∑ t ∈ s, M.K σ (f t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [M.K_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, M.K_add, ih]

/-- `T_Eⁿ 0 = ∑_{t < n} K_Eᵗ h_E`. -/
theorem iterate_T_zero (σ : M.Policy) (n : ℕ) :
    (M.T σ)^[n] 0 = ∑ t ∈ Finset.range n, (M.K σ)^[t] (M.hcost σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, Finset.sum_range_succ']
    simp only [T, M.K_sum, iterate_zero, id]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun t _ => (iterate_succ_apply' _ t _).symm

theorem sum_apply (s : Finset ℕ) (f : ℕ → BM X) (x : X) :
    (∑ t ∈ s, f t).toFun x = ∑ t ∈ s, (f t).toFun x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, BM.add_apply, ih]

omit [IsMarkovKernel M.P] in
theorem hcost_nonneg (σ : M.Policy) : 0 ≤ M.hcost σ := fun x =>
  add_nonneg (indicator_nonneg (fun y _ => M.e_nonneg y) x)
    (indicator_nonneg (fun y _ => M.c_nonneg y) x)

omit [IsMarkovKernel M.P] in
theorem norm_hcost_le (σ : M.Policy) : ‖M.hcost σ‖ ≤ ‖M.e‖ + ‖M.c‖ := by
  obtain ⟨C, hC⟩ := (M.hcost σ).bdd'
  refine BM.norm_le (add_nonneg (norm_nonneg _) (norm_nonneg _)) fun x => ?_
  simp only [hcost]
  by_cases hx : x ∈ σ.1
  · rw [indicator_of_mem hx, indicator_of_notMem (notMem_compl_iff.2 hx), add_zero]
    exact (BM.abs_le_norm _ x).trans (le_add_of_nonneg_right (norm_nonneg _))
  · rw [indicator_of_notMem hx, indicator_of_mem (mem_compl hx), zero_add]
    exact (BM.abs_le_norm _ x).trans (le_add_of_nonneg_left (norm_nonneg _))

/-- `∑_{t < n} ℙ_x{τ_E ≥ t} ≤ 1 + 𝔼_x τ̄`. -/
theorem sum_surv_le (σ : M.Policy) {C : ℝ}
    (hC : ∀ N x, ∑ n ∈ Finset.range N, (M.surv M.barPolicy (n + 1)).toFun x ≤ C) (n : ℕ)
    (x : X) : ∑ t ∈ Finset.range n, (M.surv σ t).toFun x ≤ 1 + C := by
  have hC0 : 0 ≤ C := by simpa using hC 0 x
  cases n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; linarith
  | succ m =>
    rw [Finset.sum_range_succ']
    have h0 : (M.surv σ 0).toFun x = 1 := rfl
    have h1 : ∑ t ∈ Finset.range m, (M.surv σ (t + 1)).toFun x ≤
        ∑ t ∈ Finset.range m, (M.surv M.barPolicy (t + 1)).toFun x :=
      Finset.sum_le_sum fun t _ => M.surv_le_surv_bar σ (t + 1) x
    linarith [hC m x]

/-- The bound behind **Lemma 3.2.3**: `‖T_Eⁿ 0‖ ≤ (‖e‖ + ‖c‖)(1 + C)`. -/
theorem norm_iterate_T_zero_le (σ : M.Policy) {C : ℝ}
    (hC : ∀ N x, ∑ n ∈ Finset.range N, (M.surv M.barPolicy (n + 1)).toFun x ≤ C) (n : ℕ) :
    ‖(M.T σ)^[n] 0‖ ≤ (‖M.e‖ + ‖M.c‖) * (1 + max C 0) := by
  refine BM.norm_le (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (by positivity)) fun x => ?_
  rw [M.iterate_T_zero, sum_apply]
  calc |∑ t ∈ Finset.range n, ((M.K σ)^[t] (M.hcost σ)).toFun x|
      ≤ ∑ t ∈ Finset.range n, |((M.K σ)^[t] (M.hcost σ)).toFun x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range n, ‖M.hcost σ‖ * (M.surv σ t).toFun x :=
        Finset.sum_le_sum fun t _ => M.abs_iterate_K_le σ t _ x
    _ = ‖M.hcost σ‖ * ∑ t ∈ Finset.range n, (M.surv σ t).toFun x := by rw [Finset.mul_sum]
    _ ≤ (‖M.e‖ + ‖M.c‖) * (1 + max C 0) := mul_le_mul (M.norm_hcost_le σ)
        ((M.sum_surv_le σ hC n x).trans (by linarith [le_max_left C 0]))
        (Finset.sum_nonneg fun t _ => M.surv_nonneg σ t x)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- `dist (T_E f) (T_E g) ≤ dist f g`. -/
theorem dist_T_le (σ : M.Policy) (f g : BM X) : dist (M.T σ f) (M.T σ g) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  have h := M.lemma_3_2_6 σ 1 (f - g)
  have hs : ‖M.surv σ 1‖ ≤ 1 := BM.norm_le zero_le_one fun x => by
    rw [abs_of_nonneg (M.surv_nonneg σ 1 x)]
    exact M.K_const_le σ zero_le_one x
  have hT : M.T σ f - M.T σ g = M.K σ (f - g) := by
    simpa using M.iterate_T_sub σ 1 f g
  rw [hT]
  exact h.trans (mul_le_of_le_one_right (norm_nonneg _) hs)

/-- The `σ`-loss function (3.13), as the limit of `T_Eⁿ 0 = ∑_{t < n} K_Eᵗ h_E`. -/
noncomputable def lossFn (σ : M.Policy) : BM X := limUnder atTop fun n => (M.T σ)^[n] 0

theorem tendsto_lossFn (hA : M.Assumption321) (σ : M.Policy) :
    Tendsto (fun n => (M.T σ)^[n] 0) atTop (𝓝 (M.lossFn σ)) := by
  obtain ⟨C, hC⟩ := hA
  set B := (‖M.e‖ + ‖M.c‖) * (1 + max C 0)
  have hsurv := (M.lemma_3_2_7 ⟨C, hC⟩ σ).const_mul B
  rw [mul_zero] at hsurv
  have hcauchy : CauchySeq fun n => (M.T σ)^[n] 0 := by
    refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hsurv.eventually (gt_mem_nhds hε))
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [iterate_add_apply, dist_eq_norm, M.iterate_T_sub, sub_zero]
    exact ((M.lemma_3_2_6 σ N _).trans (mul_le_mul_of_nonneg_right
      (M.norm_iterate_T_zero_le σ hC m) (norm_nonneg _))).trans_lt (hN N le_rfl)
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact tendsto_nhds_limUnder ⟨g, hg⟩

/-- **Lemma 3.2.4** (p. 112): `g_E` is a fixed point of `T_E`. -/
theorem lemma_3_2_4 (hA : M.Assumption321) (σ : M.Policy) :
    M.T σ (M.lossFn σ) = M.lossFn σ := by
  have hlim := M.tendsto_lossFn hA σ
  have hcont : Continuous (M.T σ) :=
    LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun f g => by
      simpa using M.dist_T_le σ f g)
  have h1 : Tendsto (fun n => (M.T σ)^[n + 1] 0) atTop (𝓝 (M.T σ (M.lossFn σ))) := by
    simp only [iterate_succ_apply']
    exact (hcont.tendsto _).comp hlim
  exact tendsto_nhds_unique h1 (hlim.comp (tendsto_add_atTop_nat 1))

/-- **Lemma 3.2.3** (p. 112): under Assumption 3.2.1, `g_E` is bounded:
`‖g_E‖ ≤ (‖e‖ + ‖c‖)(1 + sup_x 𝔼_x τ̄)`. -/
theorem lemma_3_2_3 (σ : M.Policy) {C : ℝ}
    (hC : ∀ N x, ∑ n ∈ Finset.range N, (M.surv M.barPolicy (n + 1)).toFun x ≤ C) :
    ‖M.lossFn σ‖ ≤ (‖M.e‖ + ‖M.c‖) * (1 + max C 0) :=
  le_of_tendsto ((M.tendsto_lossFn ⟨C, hC⟩ σ).norm)
    (Eventually.of_forall (M.norm_iterate_T_zero_le σ hC))

/-- (3.13) in series form: `g_E(x) = ∑ₜ (K_Eᵗ h_E)(x)`. -/
theorem lossFn_hasSum (hA : M.Assumption321) (σ : M.Policy) (x : X) :
    HasSum (fun t => ((M.K σ)^[t] (M.hcost σ)).toFun x) ((M.lossFn σ).toFun x) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun t => M.iterate_K_nonneg σ t
    (M.hcost_nonneg σ) x) _).2 ?_
  have hpt : Tendsto (fun n => ((M.T σ)^[n] 0).toFun x) atTop (𝓝 ((M.lossFn σ).toFun x)) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
      (fun n => by rw [Real.dist_eq]; exact BM.abs_sub_le_dist _ _ x)
      (tendsto_iff_dist_tendsto_zero.1 (M.tendsto_lossFn hA σ)))
  simpa only [M.iterate_T_zero, sum_apply] using hpt

/-- **Proposition 3.2.5** (p. 114), on `bX`: under Assumption 3.2.1 every `T_E` is globally stable,
with fixed point `g_E` (Lemma 3.2.8, Lemma 3.2.4 and Exercise A.2.1). -/
theorem proposition_3_2_5_bX (hA : M.Assumption321) (σ : M.Policy) : GloballyStable (M.T σ) :=
  exercise_A_2_1 (M.lemma_3_2_8 hA σ) (M.lemma_3_2_4 hA σ)

/-- A drift (Lyapunov) criterion for Assumption 3.2.1: if `W ≥ 0` is bounded and
`(PW)(x) + δ ≤ W(x)` off the certain exit region, then `𝔼_x τ̄ ≤ W(x)/δ ≤ ‖W‖/δ`. This plays the
role of the martingale exit-time bound (Theorem A.3.9) used in §3.2.4. -/
theorem assumption321_of_drift {W : BM X} (hW : 0 ≤ W) {δ : ℝ} (hδ : 0 < δ)
    (hdrift : ∀ x ∉ M.Ebar, markovOp M.P W.toFun x + δ ≤ W.toFun x) : M.Assumption321 := by
  have hKW : δ • M.K M.barPolicy (BM.const 1) + M.K M.barPolicy W ≤ W := fun x => by
    by_cases hx : x ∈ M.Ebar
    · simp only [BM.add_apply, BM.smul_apply, M.K_apply_mem (σ := M.barPolicy) hx, mul_zero,
        add_zero]
      exact hW x
    · simp only [BM.add_apply, BM.smul_apply, M.K_apply_notMem (σ := M.barPolicy) hx]
      have h1 : markovOp M.P (BM.const 1 : BM X).toFun x = 1 :=
        congrFun (markovOp_const M.P 1) x
      rw [h1, mul_one, add_comm]
      exact hdrift x hx
  have key : ∀ N, δ • ∑ n ∈ Finset.range N,
      (M.K M.barPolicy)^[n] (M.K M.barPolicy (BM.const 1)) + (M.K M.barPolicy)^[N] W ≤ W := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hsplit : δ • ∑ n ∈ Finset.range (N + 1),
            (M.K M.barPolicy)^[n] (M.K M.barPolicy (BM.const 1)) +
            (M.K M.barPolicy)^[N + 1] W =
          δ • M.K M.barPolicy (BM.const 1) + M.K M.barPolicy (δ • ∑ n ∈ Finset.range N,
            (M.K M.barPolicy)^[n] (M.K M.barPolicy (BM.const 1)) +
            (M.K M.barPolicy)^[N] W) := by
        rw [Finset.sum_range_succ', M.K_add, M.K_smul, M.K_sum, iterate_succ_apply',
          iterate_zero, id, smul_add]
        simp only [iterate_succ_apply']
        abel
      rw [hsplit]
      exact (add_le_add le_rfl (M.K_mono _ ih)).trans hKW
  refine ⟨‖W‖ / δ, fun N x => ?_⟩
  have h1 := key N x
  have h2 : 0 ≤ ((M.K M.barPolicy)^[N] W).toFun x := M.iterate_K_nonneg M.barPolicy N hW x
  have hsurv : ∀ n, (M.surv M.barPolicy (n + 1)).toFun x =
      ((M.K M.barPolicy)^[n] (M.K M.barPolicy (BM.const 1))).toFun x := fun n => by
    simp only [surv]
    rw [iterate_succ_apply]
  simp only [BM.add_apply, BM.smul_apply, sum_apply] at h1
  rw [le_div_iff₀ hδ]
  simp only [hsurv]
  have h3 : W.toFun x ≤ ‖W‖ := (le_abs_self _).trans (BM.abs_le_norm W x)
  nlinarith

/-! ### The ADP on `bX₊` -/

theorem Pop_nonneg {g : BM X} (hg : 0 ≤ g) : 0 ≤ M.Pop g := fun x => by
  have := markovOp_mono M.P (const_mem_bX 0) (BM.mem_bX g) hg x
  rwa [markovOp_const] at this

theorem T_nonneg (σ : M.Policy) {g : BM X} (hg : 0 ≤ g) : 0 ≤ M.T σ g :=
  add_nonneg (M.hcost_nonneg σ) (M.K_nonneg σ hg)

theorem T_mono (σ : M.Policy) : Monotone (M.T σ) := fun _ _ h =>
  add_le_add le_rfl (M.K_mono σ h)

theorem lossFn_nonneg (hA : M.Assumption321) (σ : M.Policy) : 0 ≤ M.lossFn σ :=
  ge_of_tendsto' (M.tendsto_lossFn hA σ) fun n => by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [iterate_succ_apply']
      exact M.T_nonneg σ ih

/-- The no-discount optimal stopping ADP `(bX₊, 𝕋)` (§3.2.3.5). -/
noncomputable def adp : ADP {g : BM X // 0 ≤ g} M.Policy where
  T σ g := ⟨M.T σ g.1, M.T_nonneg σ g.2⟩
  mono σ _ _ h := M.T_mono σ h
  nonempty := ⟨M.barPolicy⟩

/-- **Proposition 3.2.5** (p. 114): under Assumption 3.2.1 every `T_E` is globally stable on
`bX₊`. -/
theorem proposition_3_2_5 (hA : M.Assumption321) : M.adp.IsGloballyStable := fun σ => by
  obtain ⟨u, hu, huniq, hlim⟩ := M.proposition_3_2_5_bX hA σ
  have hit : ∀ n (g : {g : BM X // 0 ≤ g}), ((M.adp.T σ)^[n] g).1 = (M.T σ)^[n] g.1 := by
    intro n
    induction n with
    | zero => exact fun g => rfl
    | succ n ih =>
      intro g
      rw [iterate_succ_apply', iterate_succ_apply', ← ih]
      rfl
  have hu0 : u = M.lossFn σ := (huniq _ (M.lemma_3_2_4 hA σ)).symm
  refine ⟨⟨u, hu0 ▸ M.lossFn_nonneg hA σ⟩, Subtype.ext hu, fun w hw =>
    Subtype.ext (huniq w.1 (congrArg Subtype.val hw)), fun g => ?_⟩
  refine tendsto_subtype_rng.2 ?_
  simp only [hit]
  exact hlim g.1

/-- The `g`-min-greedy exit region `{e ≤ c + Pg}` (§3.2.3.5). -/
noncomputable def minGreedy (g : {g : BM X // 0 ≤ g}) : M.Policy :=
  ⟨{x | M.e.toFun x ≤ M.c.toFun x + markovOp M.P g.1.toFun x},
    measurableSet_le M.e.measurable' (M.c.measurable'.add (measurable_markovOp M.P
      g.1.measurable')),
    fun x hx => (show M.e.toFun x ≤ M.c.toFun x from hx).trans
      (le_add_of_nonneg_right (M.Pop_nonneg g.2 x))⟩

/-- (3.11): the min-greedy policy attains `min{e, c + Pg}`. -/
theorem T_minGreedy_apply (g : {g : BM X // 0 ≤ g}) (x : X) :
    (M.T (M.minGreedy g) g.1).toFun x =
      min (M.e.toFun x) (M.c.toFun x + markovOp M.P g.1.toFun x) := by
  by_cases hx : x ∈ (M.minGreedy g).1
  · rw [M.T_apply_mem hx, min_eq_left hx]
  · rw [M.T_apply_notMem hx, min_eq_right (le_of_lt (not_le.1 hx))]

/-- §3.2.3.5 (p. 114): the min-greedy exit region is `g`-min-greedy, so `(bX₊, 𝕋)` is
min-regular, and its Bellman min-operator is (3.11), `T▿g = min{e, c + Pg}`. -/
theorem isMinGreedy_minGreedy (g : {g : BM X // 0 ≤ g}) :
    M.adp.IsMinGreedy g (M.minGreedy g) := fun τ x => by
  change (M.T (M.minGreedy g) g.1).toFun x ≤ (M.T τ g.1).toFun x
  rw [M.T_minGreedy_apply]
  by_cases hx : x ∈ τ.1
  · rw [M.T_apply_mem hx]
    exact min_le_left _ _
  · rw [M.T_apply_notMem hx]
    exact min_le_right _ _

theorem adp_minRegular : M.adp.MinRegular := fun g => ⟨_, M.isMinGreedy_minGreedy g⟩

/-- `bX₊` is countably Dedekind complete. -/
theorem countablyDedekindComplete_nonneg :
    CountablyDedekindComplete {g : BM X // 0 ≤ g} := by
  intro A hne hc
  obtain ⟨a₀, ha₀⟩ := hne
  have h := BM.countablyDedekindComplete (Subtype.val '' A) ⟨a₀.1, a₀, ha₀, rfl⟩ (hc.image _)
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨l, hl⟩ => ?_⟩
  · obtain ⟨s, hs⟩ := h.1 ⟨u.1, by rintro _ ⟨a, ha, rfl⟩; exact hu ha⟩
    have hs0 : 0 ≤ s := a₀.2.trans (hs.1 ⟨a₀, ha₀, rfl⟩)
    exact ⟨⟨s, hs0⟩, fun a ha => hs.1 ⟨a, ha, rfl⟩, fun w hw =>
      hs.2 (by rintro _ ⟨a, ha, rfl⟩; exact hw ha)⟩
  · obtain ⟨i, hi⟩ := h.2 ⟨l.1, by rintro _ ⟨a, ha, rfl⟩; exact hl ha⟩
    have hi0 : 0 ≤ i := l.2.trans (hi.2 (by rintro _ ⟨a, ha, rfl⟩; exact hl ha))
    exact ⟨⟨i, hi0⟩, fun a ha => hi.1 ⟨a, ha, rfl⟩, fun w hw =>
      hi.2 (by rintro _ ⟨a, ha, rfl⟩; exact hw ha)⟩

/-- The `σ`-value function of the ADP is the `σ`-loss function `g_E`. -/
theorem vσ_eq_lossFn (hA : M.Assumption321) (σ : M.Policy) :
    (M.adp.vσ (M.proposition_3_2_5 hA).wellPosed σ).1 = M.lossFn σ :=
  (congrArg Subtype.val (M.adp.eq_vσ (M.proposition_3_2_5 hA).wellPosed
    (σ := σ) (v := ⟨M.lossFn σ, M.lossFn_nonneg hA σ⟩)
    (Subtype.ext (M.lemma_3_2_4 hA σ)))).symm

/-- **Theorem 3.2.9** (p. 116): under Assumption 3.2.1, for the no-discount optimal stopping ADP
`(bX₊, 𝕋)`, (i) the fundamental min-optimality properties hold and (ii) min-VFI, min-OPI and
min-HPI all converge. -/
theorem theorem_3_2_9 (hA : M.Assumption321) :
    M.adp.MinFundamentalOptimality (M.proposition_3_2_5 hA).wellPosed ∧
      ∃ vstar, M.adp.IsMinValueFunction vstar ∧ M.adp.MinVFIConverges vstar ∧
        ∀ g, M.adp.IsMinSelector g → M.adp.MinOPIConverges g vstar ∧
          M.adp.MinHPIConverges (M.proposition_3_2_5 hA).wellPosed g vstar :=
  ADP.theorem_3_1_8 M.adp_minRegular (M.proposition_3_2_5 hA)
    ⟨⟨0, le_rfl⟩, fun σ => M.T_nonneg σ le_rfl⟩ countablyDedekindComplete_nonneg

end NoDiscountStopping

end SargentStachurski.ADPsOnPospaces
