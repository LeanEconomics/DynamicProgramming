/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.L1Operators
import AdditionalApplications.Pospace

/-!
# Job search on `L¹(φ)`

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.1.1 and §8.1.3.1 (pp. 246–256).

The wage offer process is `P`-Markov on a state space `X` with a stationary distribution `φ`
(Assumption 8.1.2); the offer at state `x` is `w(x)`, with `w ∈ L¹(φ)` (finite mean). The iid
model of §8.1.1 (Assumption 8.1.1) is the case `P(x, ·) = φ`. The book's `W ⊆ ℝ₊` with `w(x) = x`
is the case `X = W`; signs of wages are not needed for the optimality results.

* (8.19): `T_σ v = σe + (1 − σ)(c + βPv)` with `e = w/(1 − β)`, an affine operator
  `T_σ v = r_σ + K_σ v` on `L¹(φ)` with `0 ≤ K_σ = (1 − σ)βP ≤ βP`.
* **Exercises 8.1.14–8.1.17**: `T_σ` is an order preserving self-map; the policy (8.20) is
  greedy and the Bellman operator is (8.21); `T_σ` is order continuous; `v_σ` is the Neumann
  series (8.22).
* **Proposition 8.1.2** (Theorem 4.1.8, `ρ(βP) ≤ ‖βP‖ ≤ β`).
* **Exercises 8.1.18–8.1.20**: with `w, c ≥ 0`, the order interval `[0, v̄]`,
  `v̄ = (I − βP)⁻¹(e + c)`, is invariant, contains every `v_σ`, and the optimality results hold
  on it; with `X` finite, HPI terminates.
* The iid case: **Exercises 8.1.1–8.1.3** and **Proposition 8.1.1**.
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

/-- Accept/reject policies: measurable `σ : X → Bool`, `true` meaning "accept". -/
abbrev StopPolicy (X : Type*) [MeasurableSpace X] : Type _ := {σ : X → Bool // Measurable σ}

variable {X : Type*} [MeasurableSpace X]

/-- `σ` as a `{0, 1}`-valued function. -/
def polInd (σ : StopPolicy X) (x : X) : ℝ := if σ.1 x then 1 else 0

/-- `1 − σ`. -/
def polCont (σ : StopPolicy X) (x : X) : ℝ := if σ.1 x then 0 else 1

theorem measurable_polInd (σ : StopPolicy X) : Measurable (polInd σ) :=
  Measurable.ite (σ.2 (measurableSet_singleton true)) measurable_const measurable_const

theorem measurable_polCont (σ : StopPolicy X) : Measurable (polCont σ) :=
  Measurable.ite (σ.2 (measurableSet_singleton true)) measurable_const measurable_const

theorem abs_polInd_le (σ : StopPolicy X) (x : X) : |polInd σ x| ≤ 1 := by
  simp only [polInd]; split_ifs <;> simp

theorem abs_polCont_le (σ : StopPolicy X) (x : X) : |polCont σ x| ≤ 1 := by
  simp only [polCont]; split_ifs <;> simp

theorem polCont_nonneg (σ : StopPolicy X) (x : X) : 0 ≤ polCont σ x := by
  simp only [polCont]; split_ifs <;> norm_num

theorem polCont_le_one (σ : StopPolicy X) (x : X) : polCont σ x ≤ 1 := by
  simp only [polCont]; split_ifs <;> norm_num

theorem polInd_nonneg (σ : StopPolicy X) (x : X) : 0 ≤ polInd σ x := by
  simp only [polInd]; split_ifs <;> norm_num

/-- The policy accepting where `s ≥ h`, for measurable `s` and `h`. -/
noncomputable def acceptWhere {s h : X → ℝ} (hs : Measurable s) (hh : Measurable h) :
    StopPolicy X :=
  ⟨fun x => decide (h x ≤ s x), measurable_to_bool (by
    have : (fun x => decide (h x ≤ s x)) ⁻¹' {true} = {x | h x ≤ s x} := by
      ext x
      simp
    rw [this]
    exact measurableSet_le hh hs)⟩

theorem acceptWhere_apply {s h : X → ℝ} (hs : Measurable s) (hh : Measurable h) (x : X) :
    (if (acceptWhere hs hh).1 x then s x else h x) = max (s x) (h x) := by
  by_cases hx : h x ≤ s x
  · simp [acceptWhere, hx]
  · simp only [acceptWhere, hx, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_right (le_of_not_ge hx)).symm

/-- `id` is an isometric order embedding of `L¹(φ)` into itself. -/
theorem isIsoOrderEmbedding_id_L1 (φ : Measure X) :
    BanachLattice.IsIsoOrderEmbedding (id : Lp ℝ 1 φ → Lp ℝ 1 φ) :=
  ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩

/-- The job search model with `P`-Markov offers (Assumption 8.1.2). -/
structure JobSearch (X : Type*) [MeasurableSpace X] where
  /-- the offer kernel -/
  P : Kernel X X
  [isMarkov : IsMarkovKernel P]
  /-- a stationary distribution -/
  φ : Measure X
  [isProb : IsProbabilityMeasure φ]
  stationary : φ.bind P = φ
  /-- the wage offer at each state -/
  wage : X → ℝ
  measurable_wage : Measurable wage
  integrable_wage : Integrable wage φ
  /-- unemployment compensation -/
  c : ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

namespace JobSearch

attribute [local instance] JobSearch.isMarkov JobSearch.isProb

variable (M : JobSearch X)

/-- The Markov operator `P` on `L¹(φ)`. -/
noncomputable def Pop : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ := L1.markovCLM M.stationary

/-- `K = βP`. -/
noncomputable def D : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ := M.β • M.Pop

/-- The stopping value `e(x) = w(x)/(1 − β)` (8.2). -/
noncomputable def efun (x : X) : ℝ := M.wage x / (1 - M.β)

theorem measurable_efun : Measurable M.efun := M.measurable_wage.div_const _

/-- `e ∈ L¹(φ)`. -/
noncomputable def e : Lp ℝ 1 M.φ :=
  (memLp_one_iff_integrable.2 (M.integrable_wage.div_const (1 - M.β))).toLp M.efun

/-- The constant `c` in `L¹(φ)`. -/
noncomputable def cconst : Lp ℝ 1 M.φ := (memLp_const M.c).toLp _

theorem e_coeFn : ⇑M.e =ᵐ[M.φ] M.efun :=
  (memLp_one_iff_integrable.2 (M.integrable_wage.div_const (1 - M.β))).coeFn_toLp

theorem cconst_coeFn : ⇑M.cconst =ᵐ[M.φ] fun _ => M.c := (memLp_const M.c).coeFn_toLp

/-- `r_σ = σe + (1 − σ)c`. -/
noncomputable def rσ (σ : StopPolicy X) : Lp ℝ 1 M.φ :=
  L1.mulCLM M.φ (measurable_polInd σ) (abs_polInd_le σ) M.e +
    L1.mulCLM M.φ (measurable_polCont σ) (abs_polCont_le σ) M.cconst

/-- `K_σ = (1 − σ)βP`. -/
noncomputable def Kσ (σ : StopPolicy X) : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ :=
  L1.mulCLM M.φ (measurable_polCont σ) (abs_polCont_le σ) ∘L M.D

theorem D_isPositive : BanachLattice.IsPositiveOp M.D := fun v hv => by
  have h := L1.markovCLM_isPositive M.stationary v hv
  rw [← Lp.coeFn_nonneg] at h ⊢
  filter_upwards [Lp.coeFn_smul M.β (M.Pop v), h] with x h1 h2
  change 0 ≤ (M.β • M.Pop v) x
  rw [h1, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg M.β_nonneg h2

theorem Kσ_isPositive (σ : StopPolicy X) : BanachLattice.IsPositiveOp (M.Kσ σ) := fun v hv =>
  L1.mulCLM_isPositive (measurable_polCont σ) (abs_polCont_le σ) (polCont_nonneg σ) _
    (M.D_isPositive v hv)

theorem Kσ_le_D (σ : StopPolicy X) (h : Lp ℝ 1 M.φ) (hh : 0 ≤ h) : M.Kσ σ h ≤ M.D h :=
  L1.mulCLM_le_self (measurable_polCont σ) (abs_polCont_le σ) (polCont_le_one σ)
    (M.D_isPositive h hh)

theorem norm_D_le : ‖M.D‖ ≤ M.β :=
  ContinuousLinearMap.opNorm_le_bound _ M.β_nonneg fun v => by
    change ‖M.β • M.Pop v‖ ≤ M.β * ‖v‖
    rw [norm_smul, Real.norm_of_nonneg M.β_nonneg]
    refine mul_le_mul_of_nonneg_left ((M.Pop.le_opNorm v).trans ?_) M.β_nonneg
    exact (mul_le_mul_of_nonneg_right (L1.markovCLM_norm_le M.stationary)
      (norm_nonneg v)).trans_eq (one_mul _)

/-- `ρ(βP) ≤ ‖βP‖ ≤ β < 1` (the book cites Lemma A.5.32 for `ρ(βP) = β`). -/
theorem specRad_D_lt_one : BanachLattice.specRad M.D < 1 :=
  ((BanachLattice.specRad_le_norm _).trans M.norm_D_le).trans_lt M.β_lt_one

/-- The job search ADP `(L¹(φ), 𝕋)`. -/
noncomputable def adp : ADP (Lp ℝ 1 M.φ) (StopPolicy X) where
  T σ v := M.rσ σ + M.Kσ σ v
  mono σ _ _ h := add_le_add le_rfl ((M.Kσ_isPositive σ).mono h)
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- (8.19): `T_σ v = σe + (1 − σ)(c + βPv)` almost everywhere. -/
theorem T_coeFn (σ : StopPolicy X) (v : Lp ℝ 1 M.φ) :
    ⇑(M.adp.T σ v) =ᵐ[M.φ] fun x => if σ.1 x then M.efun x else M.c + M.β * M.Pop v x := by
  filter_upwards [Lp.coeFn_add (M.rσ σ) (M.Kσ σ v),
    Lp.coeFn_add (L1.mulCLM M.φ (measurable_polInd σ) (abs_polInd_le σ) M.e)
      (L1.mulCLM M.φ (measurable_polCont σ) (abs_polCont_le σ) M.cconst),
    L1.mulCLM_coeFn (measurable_polInd σ) (abs_polInd_le σ) M.e,
    L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) M.cconst,
    L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) (M.D v),
    Lp.coeFn_smul M.β (M.Pop v), M.e_coeFn, M.cconst_coeFn]
    with x h1 h2 h3 h4 h5 h6 h7 h8
  change (M.rσ σ + M.Kσ σ v) x = _
  rw [h1, Pi.add_apply]
  change (L1.mulCLM M.φ (measurable_polInd σ) (abs_polInd_le σ) M.e +
    L1.mulCLM M.φ (measurable_polCont σ) (abs_polCont_le σ) M.cconst) x +
    (L1.mulCLM M.φ (measurable_polCont σ) (abs_polCont_le σ) (M.D v)) x = _
  rw [h2, Pi.add_apply, h3, h4, h5]
  change polInd σ x * M.e x + polCont σ x * M.cconst x + polCont σ x * (M.β • M.Pop v) x = _
  rw [h6, Pi.smul_apply, smul_eq_mul, h7, h8]
  simp only [polInd, polCont]
  split_ifs <;> ring

/-- **Exercise 8.1.14** (p. 255): `T_σ` is an order preserving self-map on `L¹(φ)`. -/
theorem exercise_8_1_14 (σ : StopPolicy X) : Monotone (M.adp.T σ) := M.adp.mono σ

/-- The policy (8.20): accept when `e ≥ c + βPv`. -/
noncomputable def accept (v : Lp ℝ 1 M.φ) : StopPolicy X :=
  acceptWhere (s := M.efun) (h := fun x => M.c + M.β * M.Pop v x) M.measurable_efun
    (measurable_const.add (measurable_const.mul (Lp.stronglyMeasurable (M.Pop v)).measurable))

theorem T_accept_coeFn (v : Lp ℝ 1 M.φ) :
    ⇑(M.adp.T (M.accept v) v) =ᵐ[M.φ] fun x => max (M.efun x) (M.c + M.β * M.Pop v x) := by
  filter_upwards [M.T_coeFn (M.accept v) v] with x hx
  rw [hx]
  exact acceptWhere_apply M.measurable_efun _ x

/-- **Exercise 8.1.15** (p. 255): the policy (8.20) is `v`-greedy, and the Bellman operator is
(8.21), `(Tv)(w) = max{w/(1 − β), c + β ∫ v(w')P(w, dw')}` almost everywhere. -/
theorem exercise_8_1_15 (v : Lp ℝ 1 M.φ) :
    M.adp.IsGreedy v (M.accept v) ∧
      ⇑(M.adp.bellman v) =ᵐ[M.φ] fun x => max (M.efun x) (M.c + M.β * M.Pop v x) := by
  have hg : M.adp.IsGreedy v (M.accept v) := fun τ => by
    rw [← Lp.coeFn_le]
    filter_upwards [M.T_coeFn τ v, M.T_accept_coeFn v] with x h1 h2
    rw [h1, h2]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine ⟨hg, ?_⟩
  have heq : M.adp.bellman v = M.adp.T (M.accept v) v :=
    le_antisymm (hg _) (M.adp.isGreedy_greedy ⟨_, hg⟩ _)
  rw [heq]
  exact M.T_accept_coeFn v

theorem regular : M.adp.Regular := fun v => ⟨_, (M.exercise_8_1_15 v).1⟩

theorem isAdditive : BanachLattice.IsAdditive id M.adp M.rσ M.Kσ :=
  ⟨M.Kσ_isPositive, fun _ _ => rfl⟩

theorem isGloballyStable : M.adp.IsGloballyStable := fun σ =>
  (BanachLattice.theorem_4_1_4 (isIsoOrderEmbedding_id_L1 M.φ)
    ⟨BanachLattice.example_4_1_1 M.D_isPositive M.specRad_D_lt_one, fun v w =>
      (M.isAdditive.abs_sub σ v w).trans (M.Kσ_le_D σ _ (abs_nonneg _))⟩).1

/-- Iterating `T_σ` from `0` gives the partial sums `∑_{t < n} K_σ^t r_σ`. -/
theorem iterate_T_zero (σ : StopPolicy X) (n : ℕ) :
    (M.adp.T σ)^[n] 0 = ∑ t ∈ Finset.range n, (M.Kσ σ ^ t) (M.rσ σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Finset.sum_range_succ']
    change M.rσ σ + M.Kσ σ (∑ t ∈ Finset.range n, (M.Kσ σ ^ t) (M.rσ σ)) = _
    rw [map_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pow_succ']
    rfl

/-- **Exercise 8.1.17** (p. 256): `T_σ` has a unique fixed point `v_σ` in `L¹(φ)`, the Neumann
series `v_σ = ∑_{t ≥ 0} [β(1 − σ)P]^t (σe + (1 − σ)c)` (8.22). -/
theorem exercise_8_1_17 (σ : StopPolicy X) :
    ∃ vσ, M.adp.T σ vσ = vσ ∧ (∀ w, M.adp.T σ w = w → w = vσ) ∧
      Tendsto (fun n => ∑ t ∈ Finset.range n, (M.Kσ σ ^ t) (M.rσ σ)) atTop (𝓝 vσ) := by
  obtain ⟨u, hu, huniq, hlim⟩ := M.isGloballyStable σ
  exact ⟨u, hu, huniq, (hlim 0).congr fun n => M.iterate_T_zero σ n⟩

/-- **Exercise 8.1.1** (p. 247) and the well-posedness claim of Proposition 8.1.2: every `T_σ` has
a unique fixed point. -/
theorem wellPosed : M.adp.WellPosed := M.isGloballyStable.wellPosed

/-- **Proposition 8.1.2** (p. 256): under Assumption 8.1.2, the job search ADP `(L¹(φ), 𝕋)` is
well-posed, (i) the fundamental optimality properties hold, and (ii) VFI, OPI and HPI all
converge (Theorem 4.1.8). -/
theorem proposition_8_1_2 :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧ ∃ vstar,
      M.adp.VFIGeometric univ vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar := by
  have hD := BanachLattice.example_4_1_1 M.D_isPositive M.specRad_D_lt_one
  have hsr : M.adp.IsSemiRegular univ := ⟨isClosed_univ, fun v _ => M.regular v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8
    (isIsoOrderEmbedding_id_L1 M.φ) M.adp M.isAdditive hD M.Kσ_le_D hsr univ_nonempty
  obtain ⟨w, -, -, -, hwG, hwb⟩ := hFO.exists_vstar
  obtain ⟨-, w', hw', hvfi, -⟩ := ADP.theorem_3_1_2 M.regular M.isGloballyStable
    ((M.adp.solvesBellman_iff hwG).1 hwb)
  obtain rfl : vstar = w' := hgeo.1.unique hw'
  exact ⟨hw, hFO, vstar, hgeo, hvfi, hconv M.regular⟩

end JobSearch

/-! ### Order continuity -/

/-- In `L¹(φ)`, an increasing sequence with supremum `v` converges to `v` in norm: the norm is
σ-order continuous (monotone convergence). -/
theorem L1.tendsto_of_monotone_isLUB {φ : Measure X} {f : ℕ → Lp ℝ 1 φ} {v : Lp ℝ 1 φ}
    (hf : Monotone f) (hv : IsLUB (range f) v) : Tendsto f atTop (𝓝 v) := by
  have hmono : ∀ᵐ x ∂φ, Monotone fun n => f n x := by
    have h2 : ∀ᵐ x ∂φ, ∀ n m, n ≤ m → f n x ≤ f m x := by
      rw [ae_all_iff]
      intro n
      rw [ae_all_iff]
      intro m
      by_cases h : n ≤ m
      · filter_upwards [(Lp.coeFn_le _ _).2 (hf h)] with x hx _ using hx
      · exact Eventually.of_forall fun x h' => absurd h' h
    filter_upwards [h2] with x hx n m h using hx n m h
  have hle : ∀ᵐ x ∂φ, ∀ n, f n x ≤ v x := ae_all_iff.2 fun n => (Lp.coeFn_le _ _).2 (hv.1 ⟨n, rfl⟩)
  -- the pointwise limit `g = sup_n f_n`
  let g : X → ℝ := fun x => ⨆ n, f n x
  have hlim : ∀ᵐ x ∂φ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    filter_upwards [hmono, hle] with x h1 h2
    exact tendsto_atTop_ciSup h1 ⟨v x, by rintro _ ⟨n, rfl⟩; exact h2 n⟩
  have hgle : ∀ᵐ x ∂φ, g x ≤ v x := by
    filter_upwards [hle] with x h2
    exact ciSup_le h2
  have hge : ∀ᵐ x ∂φ, ∀ n, f n x ≤ g x := by
    filter_upwards [hle] with x h2 n
    exact le_ciSup ⟨v x, by rintro _ ⟨m, rfl⟩; exact h2 m⟩ n
  have hgm : AEStronglyMeasurable g φ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => Lp.aestronglyMeasurable (f n)) hlim
  have hgi : Integrable g φ := by
    refine ((L1.integrable_coeFn (f 0)).norm.add (L1.integrable_coeFn v).norm).mono' hgm ?_
    filter_upwards [hge, hgle] with x h1 h2
    rw [Real.norm_eq_abs, abs_le]
    have h3 := h1 0
    constructor <;> simp only [Pi.add_apply, Real.norm_eq_abs] <;>
      linarith [neg_abs_le (f 0 x), le_abs_self (v x), abs_nonneg (f 0 x), abs_nonneg (v x)]
  have hGcoe := hgi.coeFn_toL1
  -- `v` is the class of `g`
  have hvG : v = hgi.toL1 g := by
    refine le_antisymm (hv.2 ?_) ((Lp.coeFn_le _ _).1 ?_)
    · rintro _ ⟨n, rfl⟩
      refine (Lp.coeFn_le _ _).1 ?_
      filter_upwards [hge, hGcoe] with x h1 h2
      rw [h2]
      exact h1 n
    · filter_upwards [hGcoe, hgle] with x h1 h2
      rw [h1]
      exact h2
  have hvg : ∀ᵐ x ∂φ, v x = g x := by
    rw [hvG]
    exact hGcoe
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ n, ‖f n - v‖ = ∫ x, |f n x - v x| ∂φ := fun n => by
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (f n) v] with x hx
    rw [hx, Pi.sub_apply, Real.norm_eq_abs]
  simp_rw [hnorm]
  have := tendsto_integral_of_dominated_convergence (μ := φ)
    (F := fun n x => |f n x - v x|) (f := fun _ => (0 : ℝ)) (fun x => |f 0 x - v x|)
    (fun n => continuous_abs.comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable (f n)).sub (Lp.aestronglyMeasurable v)))
    ((L1.integrable_coeFn (f 0)).sub (L1.integrable_coeFn v)).abs
    (fun n => by
      filter_upwards [hle, hmono] with x h1 h2
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonpos (sub_nonpos.2 (h1 n)),
        abs_of_nonpos (sub_nonpos.2 (h1 0))]
      linarith [h2 (Nat.zero_le n)])
    (by
      filter_upwards [hlim, hvg] with x h1 h2
      have := (h1.sub_const (v x)).abs
      rwa [← h2, sub_self, abs_zero] at this)
  simpa using this

namespace JobSearch

attribute [local instance] JobSearch.isMarkov JobSearch.isProb

variable (M : JobSearch X)

/-- **Exercise 8.1.16** (p. 256): every policy operator `T_σ` is order continuous on `L¹(φ)`. -/
theorem exercise_8_1_16 (σ : StopPolicy X) : OrderContinuous (M.adp.T σ) := fun f v hf hv => by
  have hcont : Continuous (M.adp.T σ) := continuous_const.add (M.Kσ σ).continuous
  exact isLUB_of_tendsto_of_le (hcont.continuousAt.tendsto.comp
    (L1.tendsto_of_monotone_isLUB hf hv)) fun n => M.adp.mono σ (hv.1 ⟨n, rfl⟩)

/-! ### The order interval `[0, v̄]` -/

/-- `v ↦ e + c + βPv`, a contraction of modulus `β`. -/
noncomputable def Sbar (v : Lp ℝ 1 M.φ) : Lp ℝ 1 M.φ := M.e + M.cconst + M.D v

theorem Sbar_contracting : ContractingWith ⟨M.β, M.β_nonneg⟩ M.Sbar := by
  refine ⟨M.β_lt_one, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, Sbar, Sbar, add_sub_add_left_eq_sub, ← map_sub]
  exact (M.D.le_opNorm _).trans (mul_le_mul_of_nonneg_right M.norm_D_le (norm_nonneg _))

/-- `v̄ = (I − βP)⁻¹(e + c)`: the unique solution of `v̄ = e + c + βPv̄`. -/
noncomputable def vbar : Lp ℝ 1 M.φ := ContractingWith.fixedPoint M.Sbar M.Sbar_contracting

theorem vbar_eq : M.vbar = M.e + M.cconst + M.D M.vbar :=
  (ContractingWith.fixedPoint_isFixedPt M.Sbar_contracting).symm

theorem e_nonneg (hw : ∀ x, 0 ≤ M.wage x) : 0 ≤ M.e := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [M.e_coeFn] with x hx
  rw [hx]
  exact div_nonneg (hw x) (sub_nonneg.2 M.β_lt_one.le)

theorem cconst_nonneg (hc : 0 ≤ M.c) : 0 ≤ M.cconst := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [M.cconst_coeFn] with x hx
  rw [hx]
  exact hc

theorem vbar_nonneg (hw : ∀ x, 0 ≤ M.wage x) (hc : 0 ≤ M.c) : 0 ≤ M.vbar := by
  have hpos : ∀ n, 0 ≤ M.Sbar^[n] 0 := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact add_nonneg (add_nonneg (M.e_nonneg hw) (M.cconst_nonneg hc)) (M.D_isPositive _ ih)
  exact ge_of_tendsto' (ContractingWith.tendsto_iterate_fixedPoint M.Sbar_contracting 0) hpos

/-- `T_σ v ≤ e + c + βPv` when `w, c ≥ 0` and `v ≥ 0`. -/
theorem T_le_Sbar (hw : ∀ x, 0 ≤ M.wage x) (hc : 0 ≤ M.c) (σ : StopPolicy X) {v : Lp ℝ 1 M.φ}
    (hv : 0 ≤ v) : M.adp.T σ v ≤ M.Sbar v := by
  rw [← Lp.coeFn_le]
  have hD := M.D_isPositive v hv
  rw [← Lp.coeFn_nonneg] at hD
  filter_upwards [M.T_coeFn σ v, Lp.coeFn_add (M.e + M.cconst) (M.D v),
    Lp.coeFn_add M.e M.cconst, M.e_coeFn, M.cconst_coeFn, Lp.coeFn_smul M.β (M.Pop v), hD]
    with x h1 h2 h3 h4 h5 h6 h7
  change _ ≤ (M.e + M.cconst + M.D v) x
  rw [h1, h2, Pi.add_apply, h3, Pi.add_apply, h4, h5]
  have h8 : (M.D v) x = M.β * M.Pop v x := by
    change (M.β • M.Pop v) x = _
    rw [h6, Pi.smul_apply, smul_eq_mul]
  rw [h8] at h7 ⊢
  have h7' : (0 : ℝ) ≤ M.β * M.Pop v x := h7
  have he : 0 ≤ M.efun x := div_nonneg (hw x) (sub_nonneg.2 M.β_lt_one.le)
  split_ifs <;> linarith

theorem T_nonneg (hw : ∀ x, 0 ≤ M.wage x) (hc : 0 ≤ M.c) (σ : StopPolicy X) {v : Lp ℝ 1 M.φ}
    (hv : 0 ≤ v) : 0 ≤ M.adp.T σ v := by
  rw [← Lp.coeFn_nonneg]
  have hD := M.D_isPositive v hv
  rw [← Lp.coeFn_nonneg] at hD
  filter_upwards [M.T_coeFn σ v, Lp.coeFn_smul M.β (M.Pop v), hD] with x h1 h2 h3
  rw [h1]
  have h4 : (M.D v) x = M.β * M.Pop v x := by
    change (M.β • M.Pop v) x = _
    rw [h2, Pi.smul_apply, smul_eq_mul]
  rw [h4] at h3
  have h3' : (0 : ℝ) ≤ M.β * M.Pop v x := h3
  split_ifs
  · exact div_nonneg (hw x) (sub_nonneg.2 M.β_lt_one.le)
  · change (0 : ℝ) ≤ M.c + M.β * M.Pop v x
    linarith

/-- **Exercise 8.1.18** (p. 256): if wages and `c` are nonnegative, then `v_σ ≤ v̄` for every `σ`
and every `T_σ` maps `V = [0, v̄]` into itself. -/
theorem exercise_8_1_18 (hw : ∀ x, 0 ≤ M.wage x) (hc : 0 ≤ M.c) :
    (∀ σ, M.adp.vσ M.wellPosed σ ≤ M.vbar) ∧
      ∀ σ v, 0 ≤ v → v ≤ M.vbar → 0 ≤ M.adp.T σ v ∧ M.adp.T σ v ≤ M.vbar := by
  have hTv : ∀ σ, M.adp.T σ M.vbar ≤ M.vbar := fun σ => by
    have := M.T_le_Sbar hw hc σ (M.vbar_nonneg hw hc)
    rwa [show M.Sbar M.vbar = M.vbar from (M.vbar_eq).symm] at this
  refine ⟨fun σ => M.isGloballyStable.isOrderStable.vσ_le σ M.vbar (hTv σ),
    fun σ v hv0 hv => ⟨M.T_nonneg hw hc σ hv0, (M.adp.mono σ hv).trans (hTv σ)⟩⟩

/-- The ADP `(V, 𝕋)` on `V = [0, v̄]` (Exercise 8.1.18). -/
noncomputable def adpV (hw : ∀ x, 0 ≤ M.wage x) (hc : 0 ≤ M.c) :
    ADP (Icc 0 M.vbar) (StopPolicy X) where
  T σ v := ⟨M.adp.T σ v, (M.exercise_8_1_18 hw hc).2 σ v v.2.1 v.2.2⟩
  mono σ _ _ h := M.adp.mono σ h
  nonempty := M.adp.nonempty

/-- **Exercise 8.1.19** (p. 256): the optimality results hold for `(V, 𝕋)`, `V = [0, v̄]`: the
fundamental optimality properties hold and VFI, OPI and HPI converge (Theorem 4.1.8 on the
closed order interval). -/
theorem exercise_8_1_19 (hw : ∀ x, 0 ≤ M.wage x) (hc : 0 ≤ M.c) :
    ∃ hw' : (M.adpV hw hc).WellPosed, (M.adpV hw hc).FundamentalOptimality hw' ∧ ∃ vstar,
      (M.adpV hw hc).VFIGeometric univ vstar ∧
        ∀ g, (M.adpV hw hc).IsSelector g →
          (M.adpV hw hc).OPIConverges g vstar ∧ (M.adpV hw hc).HPIConverges hw' g vstar := by
  have : CompleteSpace (Icc 0 M.vbar) := isClosed_Icc.completeSpace_coe
  have : Nonempty (Icc 0 M.vbar) := ⟨⟨0, le_rfl, M.vbar_nonneg hw hc⟩⟩
  have hι : BanachLattice.IsIsoOrderEmbedding (Subtype.val : Icc 0 M.vbar → Lp ℝ 1 M.φ) :=
    ⟨fun v w => dist_eq_norm (v : Lp ℝ 1 M.φ) w, fun _ _ => Iff.rfl⟩
  have hadd : BanachLattice.IsAdditive Subtype.val (M.adpV hw hc) M.rσ M.Kσ :=
    ⟨M.Kσ_isPositive, fun _ _ => rfl⟩
  have hreg : (M.adpV hw hc).Regular := fun v => ⟨M.accept v, fun τ =>
    (M.exercise_8_1_15 v).1 τ⟩
  have hsr : (M.adpV hw hc).IsSemiRegular univ :=
    ⟨isClosed_univ, fun v _ => hreg v, mapsTo_univ _ _⟩
  obtain ⟨hw', hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8 hι (M.adpV hw hc) hadd
    (BanachLattice.example_4_1_1 M.D_isPositive M.specRad_D_lt_one) M.Kσ_le_D hsr univ_nonempty
  exact ⟨hw', hFO, vstar, hgeo, hconv hreg⟩

/-- **Exercise 8.1.20** (p. 256): if the state space is finite, HPI converges in finitely many
steps: from every `v ∈ V_U`, some iterate of Howard's operator is the value function
(Theorem 2.2.6). -/
theorem exercise_8_1_20 [Finite X] :
    M.adp.FundamentalOptimality M.isGloballyStable.isOrderStable.wellPosed ∧
      ∀ g, M.adp.IsSelector g → ∀ v ∈ M.adp.VU,
        ∃ n, M.adp.IsValueFunction ((M.adp.howard M.isGloballyStable.isOrderStable.wellPosed g)^[n]
          v) :=
  ADP.fundamentalOptimality_of_finite M.isGloballyStable.isOrderStable M.regular
    (Set.finite_range _)

/-! ### The iid model -/

/-- The iid job search model (Assumption 8.1.1): offers drawn from `φ` each period, as the
Markov model with `P(x, ·) = φ`. -/
noncomputable abbrev iid (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    JobSearch X where
  P := Kernel.const X φ
  φ := φ
  stationary := by
    change φ.bind (fun _ => φ) = φ
    rw [Measure.bind_const, measure_univ, one_smul]
  wage := wage
  measurable_wage := hm
  integrable_wage := hi
  c := c
  β := β
  β_nonneg := hβ0
  β_lt_one := hβ1

/-- In the iid model, `Pv = ∫ v dφ` almost everywhere. -/
theorem iid_Pop_coeFn (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (v : Lp ℝ 1 φ) :
    ⇑((iid φ wage hm hi c β hβ0 hβ1).Pop v) =ᵐ[φ] fun _ => ∫ y, v y ∂φ :=
  L1.markovCLM_coeFn _ v

/-- **Exercises 8.1.2–8.1.3** (p. 247): in the iid model the policy (8.5),
`σ(w) = 𝟙{w/(1 − β) ≥ c + β ∫ v dφ}`, is `v`-greedy, and the Bellman operator is (8.7),
`(Tv)(w) = max{w/(1 − β), c + β ∫ v dφ}`. -/
theorem exercise_8_1_2_3 (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (v : Lp ℝ 1 φ) :
    (iid φ wage hm hi c β hβ0 hβ1).adp.IsGreedy v ((iid φ wage hm hi c β hβ0 hβ1).accept v) ∧
      ⇑((iid φ wage hm hi c β hβ0 hβ1).adp.bellman v) =ᵐ[φ]
        fun x => max (wage x / (1 - β)) (c + β * ∫ y, v y ∂φ) := by
  obtain ⟨hg, hT⟩ := (iid φ wage hm hi c β hβ0 hβ1).exercise_8_1_15 v
  refine ⟨hg, ?_⟩
  filter_upwards [hT, iid_Pop_coeFn φ wage hm hi c β hβ0 hβ1 v] with x h1 h2
  rw [h1, h2]
  rfl

/-- **Exercise 8.1.1** (p. 247) and **Proposition 8.1.1** (p. 249): under Assumption 8.1.1 the
iid job search ADP `(L¹(φ), 𝕋)` is well-posed, the fundamental optimality properties hold, and
VFI, OPI and HPI all converge. -/
theorem proposition_8_1_1 (φ : Measure X) [IsProbabilityMeasure φ] (wage : X → ℝ)
    (hm : Measurable wage) (hi : Integrable wage φ) (c β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ hw : (iid φ wage hm hi c β hβ0 hβ1).adp.WellPosed,
      (iid φ wage hm hi c β hβ0 hβ1).adp.FundamentalOptimality hw ∧ ∃ vstar,
        (iid φ wage hm hi c β hβ0 hβ1).adp.VFIConverges vstar ∧
        ∀ g, (iid φ wage hm hi c β hβ0 hβ1).adp.IsSelector g →
          (iid φ wage hm hi c β hβ0 hβ1).adp.OPIConverges g vstar ∧
            (iid φ wage hm hi c β hβ0 hβ1).adp.HPIConverges hw g vstar := by
  obtain ⟨hw, hFO, vstar, -, hvfi, hconv⟩ := (iid φ wage hm hi c β hβ0 hβ1).proposition_8_1_2
  exact ⟨hw, hFO, vstar, hvfi, hconv⟩

end JobSearch

end SargentStachurski.AdditionalApplications
