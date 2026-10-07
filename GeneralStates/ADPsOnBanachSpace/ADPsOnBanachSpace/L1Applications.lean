/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPsOnBanachSpace.L1Operators
import ADPsOnBanachSpace.FirmProblem

/-!
# Firm valuation with unbounded rewards and a real option problem

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §4.2.1.2 and §4.2.2 (pp. 134–140).

Both problems live in `L¹(ψ)` for a stationary distribution `ψ` of the state kernel `P`, with the
`ψ`-a.e. order.

* §4.2.1.2: the firm ADP `(L¹(ψ), 𝕋_FV)` with `T_σ v = σs + (1 − σ)(π + βPv)` and `π ∈ L¹(ψ)`. It is
  regular, `K_σ = (1 − σ)βP ≤ βP` and `‖βP‖ ≤ β < 1`, so Theorem 4.1.8 gives the claims of
  Proposition 4.2.1.
* §4.2.2: the real option ADP `(L¹(φ), 𝕋_RO)` with `T_σ v = −c + K(σq + (1 − σ)v)` (4.16),
  `(Kv)(x) = β(x) ∫ v(x')P(x, dx')` and `q = (I − K)⁻¹π`. **Exercise 4.2.2** (well-posedness and
  the lifetime values), **Exercise 4.2.3** (the greedy policy `𝟙{q ≥ v}`), the Bellman equation
  (4.18)–(4.19) and **Proposition 4.2.3** (via Theorem 4.1.8).
* (4.17) and the proof of Proposition 4.2.3 write the constant term as `−c + K_σ q`; it is
  `−c + K(σq)` (`RealOption.eq_4_17_misprint`).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.ADPsOnBanachSpace

variable {X : Type*} [MeasurableSpace X]

/-! ### Indicator functions of policies -/

/-- `σ` as a `{0, 1}`-valued function. -/
def polInd (σ : FirmPolicy X) (x : X) : ℝ := if σ.1 x then 1 else 0

/-- `1 − σ`. -/
def polCont (σ : FirmPolicy X) (x : X) : ℝ := if σ.1 x then 0 else 1

theorem measurable_polInd (σ : FirmPolicy X) : Measurable (polInd σ) :=
  Measurable.ite (σ.2 (measurableSet_singleton true)) measurable_const measurable_const

theorem measurable_polCont (σ : FirmPolicy X) : Measurable (polCont σ) :=
  Measurable.ite (σ.2 (measurableSet_singleton true)) measurable_const measurable_const

theorem abs_polInd_le (σ : FirmPolicy X) (x : X) : |polInd σ x| ≤ 1 := by
  simp only [polInd]; split_ifs <;> simp

theorem abs_polCont_le (σ : FirmPolicy X) (x : X) : |polCont σ x| ≤ 1 := by
  simp only [polCont]; split_ifs <;> simp

theorem polCont_nonneg (σ : FirmPolicy X) (x : X) : 0 ≤ polCont σ x := by
  simp only [polCont]; split_ifs <;> norm_num

theorem polCont_le_one (σ : FirmPolicy X) (x : X) : polCont σ x ≤ 1 := by
  simp only [polCont]; split_ifs <;> norm_num

theorem polInd_nonneg (σ : FirmPolicy X) (x : X) : 0 ≤ polInd σ x := by
  simp only [polInd]; split_ifs <;> norm_num

/-- `id` is an isometric order embedding of `L¹(ψ)` into itself. -/
theorem isIsoOrderEmbedding_id_L1 (ψ : Measure X) :
    BanachLattice.IsIsoOrderEmbedding (id : Lp ℝ 1 ψ → Lp ℝ 1 ψ) :=
  ⟨fun v w => dist_eq_norm v w, fun _ _ => Iff.rfl⟩

/-! ### Firm valuation in `L¹(ψ)` -/

/-- The firm problem with an integrable profit function (§4.2.1.2). -/
structure FirmL1 (X : Type*) [MeasurableSpace X] where
  /-- the state kernel -/
  P : Kernel X X
  isMarkov : IsMarkovKernel P
  /-- a stationary distribution -/
  ψ : Measure X
  isProb : IsProbabilityMeasure ψ
  stationary : ψ.bind P = ψ
  /-- the profit function `π ∈ L¹(ψ)` -/
  profit : Lp ℝ 1 ψ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the sale price -/
  s : ℝ

namespace FirmL1

variable (F : FirmL1 X)

/-- The Markov operator on `L¹(ψ)`. -/
noncomputable def Pop : Lp ℝ 1 F.ψ →L[ℝ] Lp ℝ 1 F.ψ :=
  have := F.isMarkov
  L1.markovCLM F.stationary

/-- The constant `s` as an element of `L¹(ψ)`. -/
noncomputable def sconst : Lp ℝ 1 F.ψ :=
  have := F.isProb
  (memLp_const F.s).toLp _

/-- The discount operator `D = βP`. -/
noncomputable def D : Lp ℝ 1 F.ψ →L[ℝ] Lp ℝ 1 F.ψ := F.β • F.Pop

/-- `r_σ = σs + (1 − σ)π`. -/
noncomputable def rσ (σ : FirmPolicy X) : Lp ℝ 1 F.ψ :=
  L1.mulCLM F.ψ (measurable_polInd σ) (abs_polInd_le σ) F.sconst +
    L1.mulCLM F.ψ (measurable_polCont σ) (abs_polCont_le σ) F.profit

/-- `K_σ = (1 − σ)βP` (4.12). -/
noncomputable def Kσ (σ : FirmPolicy X) : Lp ℝ 1 F.ψ →L[ℝ] Lp ℝ 1 F.ψ :=
  L1.mulCLM F.ψ (measurable_polCont σ) (abs_polCont_le σ) ∘L F.D

theorem D_isPositive : BanachLattice.IsPositiveOp F.D := fun v hv => by
  have := F.isMarkov
  have h := L1.markovCLM_isPositive F.stationary v hv
  rw [← Lp.coeFn_nonneg] at h ⊢
  filter_upwards [Lp.coeFn_smul F.β (F.Pop v), h] with x h1 h2
  change 0 ≤ (F.β • F.Pop v) x
  rw [h1, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg F.β_nonneg h2

theorem Kσ_isPositive (σ : FirmPolicy X) : BanachLattice.IsPositiveOp (F.Kσ σ) := fun v hv =>
  L1.mulCLM_isPositive (measurable_polCont σ) (abs_polCont_le σ) (polCont_nonneg σ) _
    (F.D_isPositive v hv)

theorem Kσ_le_D (σ : FirmPolicy X) (h : Lp ℝ 1 F.ψ) (hh : 0 ≤ h) : F.Kσ σ h ≤ F.D h :=
  L1.mulCLM_le_self (measurable_polCont σ) (abs_polCont_le σ) (polCont_le_one σ)
    (F.D_isPositive h hh)

/-- `ρ(βP) ≤ ‖βP‖ ≤ β < 1` (Lemma A.5.32 gives `ρ(βP) = β`). -/
theorem specRad_D_lt_one : BanachLattice.specRad F.D < 1 := by
  have hD : ‖F.D‖ ≤ F.β := ContinuousLinearMap.opNorm_le_bound _ F.β_nonneg fun v => by
    change ‖F.β • F.Pop v‖ ≤ F.β * ‖v‖
    rw [norm_smul, Real.norm_of_nonneg F.β_nonneg]
    refine mul_le_mul_of_nonneg_left ((F.Pop.le_opNorm v).trans ?_) F.β_nonneg
    exact (mul_le_mul_of_nonneg_right (L1.markovCLM_norm_le F.stationary)
      (norm_nonneg v)).trans_eq (one_mul _)
  exact ((BanachLattice.specRad_le_norm _).trans hD).trans_lt F.β_lt_one

/-- The firm ADP `(L¹(ψ), 𝕋_FV)`. -/
noncomputable def adp : ADP (Lp ℝ 1 F.ψ) (FirmPolicy X) where
  T σ v := F.rσ σ + F.Kσ σ v
  mono σ _ _ h := add_le_add le_rfl ((F.Kσ_isPositive σ).mono h)
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- `T_σ v = σs + (1 − σ)(π + βPv)` almost everywhere. -/
theorem T_coeFn (σ : FirmPolicy X) (v : Lp ℝ 1 F.ψ) :
    ⇑(F.adp.T σ v) =ᵐ[F.ψ] fun x => if σ.1 x then F.s else F.profit x + F.β * F.Pop v x := by
  have := F.isProb
  filter_upwards [Lp.coeFn_add (F.rσ σ) (F.Kσ σ v),
    Lp.coeFn_add (L1.mulCLM F.ψ (measurable_polInd σ) (abs_polInd_le σ) F.sconst)
      (L1.mulCLM F.ψ (measurable_polCont σ) (abs_polCont_le σ) F.profit),
    L1.mulCLM_coeFn (measurable_polInd σ) (abs_polInd_le σ) F.sconst,
    L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) F.profit,
    L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) (F.D v),
    Lp.coeFn_smul F.β (F.Pop v), (memLp_const (μ := F.ψ) F.s).coeFn_toLp]
    with x h1 h2 h3 h4 h5 h6 h7
  change (F.rσ σ + F.Kσ σ v) x = _
  rw [h1, Pi.add_apply]
  change (L1.mulCLM F.ψ (measurable_polInd σ) (abs_polInd_le σ) F.sconst +
    L1.mulCLM F.ψ (measurable_polCont σ) (abs_polCont_le σ) F.profit) x +
    (L1.mulCLM F.ψ (measurable_polCont σ) (abs_polCont_le σ) (F.D v)) x = _
  rw [h2, Pi.add_apply, h3, h4, h5]
  change polInd σ x * F.sconst x + polCont σ x * F.profit x + polCont σ x * (F.β • F.Pop v) x = _
  rw [h6, Pi.smul_apply, smul_eq_mul]
  change polInd σ x * ((memLp_const (μ := F.ψ) F.s).toLp _) x + _ + _ = _
  rw [h7]
  simp only [polInd, polCont]
  split_ifs <;> ring

/-- The `v`-greedy policy (4.11): sell when `s ≥ π + βPv`. -/
noncomputable def sell (v : Lp ℝ 1 F.ψ) : FirmPolicy X :=
  ⟨fun x => decide (F.profit x + F.β * F.Pop v x ≤ F.s), measurable_to_bool (by
    have : (fun x => decide (F.profit x + F.β * F.Pop v x ≤ F.s)) ⁻¹' {true} =
        {x | F.profit x + F.β * F.Pop v x ≤ F.s} := by
      ext x
      simp
    rw [this]
    exact measurableSet_le ((Lp.stronglyMeasurable _).measurable.add
      (measurable_const.mul (Lp.stronglyMeasurable _).measurable)) measurable_const)⟩

theorem T_sell_coeFn (v : Lp ℝ 1 F.ψ) :
    ⇑(F.adp.T (F.sell v) v) =ᵐ[F.ψ] fun x => max F.s (F.profit x + F.β * F.Pop v x) := by
  filter_upwards [F.T_coeFn (F.sell v) v] with x hx
  rw [hx]
  by_cases h : F.profit x + F.β * F.Pop v x ≤ F.s
  · simp [sell, h]
  · simp only [sell, h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (max_eq_right (le_of_not_ge h)).symm

theorem sell_isGreedy (v : Lp ℝ 1 F.ψ) : F.adp.IsGreedy v (F.sell v) := fun τ => by
  rw [← Lp.coeFn_le]
  filter_upwards [F.T_coeFn τ v, F.T_sell_coeFn v] with x h1 h2
  rw [h1, h2]
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem adp_regular : F.adp.Regular := fun v => ⟨_, F.sell_isGreedy v⟩

/-- (4.13) in `L¹(ψ)`: the Bellman operator is `Tv = s ∨ (π + βPv)` almost everywhere. -/
theorem adp_bellman_coeFn (v : Lp ℝ 1 F.ψ) :
    ⇑(F.adp.bellman v) =ᵐ[F.ψ] fun x => max F.s (F.profit x + F.β * F.Pop v x) := by
  have heq : F.adp.bellman v = F.adp.T (F.sell v) v :=
    le_antisymm (F.sell_isGreedy v _) (F.adp.isGreedy_greedy (F.adp_regular v) _)
  rw [heq]
  exact F.T_sell_coeFn v

theorem isAdditive : BanachLattice.IsAdditive id F.adp F.rσ F.Kσ :=
  ⟨F.Kσ_isPositive, fun _ _ => rfl⟩

/-- §4.2.1.2 (p. 135): the claims of Proposition 4.2.1 extend to `(L¹(ψ), 𝕋_FV)`, by
Theorem 4.1.8: the fundamental optimality properties hold, VFI converges (geometrically), and OPI
and HPI converge. -/
theorem optimality :
    ∃ hw : F.adp.WellPosed, F.adp.FundamentalOptimality hw ∧ ∃ vstar,
      F.adp.VFIGeometric univ vstar ∧ F.adp.VFIConverges vstar ∧
        ∀ g, F.adp.IsSelector g → F.adp.OPIConverges g vstar ∧ F.adp.HPIConverges hw g vstar := by
  have hD := BanachLattice.example_4_1_1 F.D_isPositive F.specRad_D_lt_one
  have hsr : F.adp.IsSemiRegular univ :=
    ⟨isClosed_univ, fun v _ => F.adp_regular v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8
    (isIsoOrderEmbedding_id_L1 F.ψ) F.adp F.isAdditive hD F.Kσ_le_D hsr univ_nonempty
  have hgs : F.adp.IsGloballyStable := fun σ =>
    (BanachLattice.theorem_4_1_4 (isIsoOrderEmbedding_id_L1 F.ψ) ⟨hD, fun v w =>
      (F.isAdditive.abs_sub σ v w).trans (F.Kσ_le_D σ _ (abs_nonneg _))⟩).1
  obtain ⟨w, -, -, -, hwG, hwb⟩ := hFO.exists_vstar
  obtain ⟨-, w', hw', hvfi, -⟩ := ADP.theorem_3_1_2 F.adp_regular hgs
    ((F.adp.solvesBellman_iff hwG).1 hwb)
  obtain rfl : vstar = w' := hgeo.1.unique hw'
  exact ⟨hw, hFO, vstar, hgeo, hvfi, hconv F.adp_regular⟩

end FirmL1

/-! ### A real option problem -/

/-- `(v ↦ a + Kv)ᵏ u − (v ↦ a + Kv)ᵏ w = Kᵏ(u − w)`. -/
theorem iterate_affine_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E)
    (K : E →L[ℝ] E) (k : ℕ) (u w : E) :
    (fun v => a + K v)^[k] u - (fun v => a + K v)^[k] w = (K ^ k) (u - w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', add_sub_add_left_eq_sub, ← map_sub, ih,
      pow_succ']
    rfl

/-- The real option problem (§4.2.2): Assumption 4.2.2, with a stationary distribution `φ`,
integrable `c` and `π`, and a bounded nonnegative measurable discount function `β`. -/
structure RealOption (X : Type*) [MeasurableSpace X] where
  /-- the state kernel -/
  P : Kernel X X
  isMarkov : IsMarkovKernel P
  /-- the stationary distribution -/
  φ : Measure X
  isProb : IsProbabilityMeasure φ
  stationary : φ.bind P = φ
  /-- the development cost -/
  c : Lp ℝ 1 φ
  /-- the post-launch profit -/
  profit : Lp ℝ 1 φ
  /-- the discount function -/
  βf : X → ℝ
  βf_meas : Measurable βf
  βf_nonneg : ∀ x, 0 ≤ βf x
  /-- a bound on the discount function -/
  N : ℝ
  βf_le : ∀ x, βf x ≤ N

namespace RealOption

variable (R : RealOption X)

theorem abs_βf_le (x : X) : |R.βf x| ≤ R.N := by
  rw [abs_of_nonneg (R.βf_nonneg x)]
  exact R.βf_le x

/-- The discount operator `(Kv)(x) = β(x) ∫ v(x')P(x, dx')` on `L¹(φ)`. -/
noncomputable def K : Lp ℝ 1 R.φ →L[ℝ] Lp ℝ 1 R.φ :=
  L1.mulCLM R.φ R.βf_meas R.abs_βf_le ∘L L1.markovCLM R.stationary

theorem K_isPositive : BanachLattice.IsPositiveOp R.K := fun v hv =>
  L1.mulCLM_isPositive R.βf_meas R.abs_βf_le R.βf_nonneg _
    (L1.markovCLM_isPositive R.stationary v hv)

/-- Under Assumption 4.2.3, `q = π + Kq` has a solution, `q = (I − K)⁻¹π`. -/
theorem exists_q (hρ : BanachLattice.specRad R.K < 1) : ∃ q, q = R.profit + R.K q := by
  obtain ⟨k, hk, hlt⟩ := BanachLattice.exercise_A_4_2 hρ
  obtain ⟨-, q, hq, -⟩ := theorem_4_1_1 (S := fun v => R.profit + R.K v) hk (norm_nonneg _) hlt
    fun u w => by
      rw [dist_eq_norm, dist_eq_norm, iterate_affine_sub]
      exact (R.K ^ k).le_opNorm _
  exact ⟨q, hq.symm⟩

/-- The value of launching, `q = (I − K)⁻¹π`. -/
noncomputable def q (hρ : BanachLattice.specRad R.K < 1) : Lp ℝ 1 R.φ :=
  (R.exists_q hρ).choose

theorem q_eq (hρ : BanachLattice.specRad R.K < 1) : R.q hρ = R.profit + R.K (R.q hρ) :=
  (R.exists_q hρ).choose_spec

variable (hρ : BanachLattice.specRad R.K < 1)

/-- The constant term `r_σ = −c + K(σq)`. -/
noncomputable def rσ (σ : FirmPolicy X) : Lp ℝ 1 R.φ :=
  -R.c + R.K (L1.mulCLM R.φ (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ))

/-- `K_σ f = K((1 − σ)f)`, `(K_σ f)(x) = β(x) ∫ f(x')(1 − σ(x'))P(x, dx')`. -/
noncomputable def Kσ (σ : FirmPolicy X) : Lp ℝ 1 R.φ →L[ℝ] Lp ℝ 1 R.φ :=
  R.K ∘L L1.mulCLM R.φ (measurable_polCont σ) (abs_polCont_le σ)

/-- The real option ADP `(L¹(φ), 𝕋_RO)`. -/
noncomputable def adp : ADP (Lp ℝ 1 R.φ) (FirmPolicy X) where
  T σ v := R.rσ hρ σ + R.Kσ σ v
  mono σ _ _ h := add_le_add le_rfl (R.K_isPositive.mono
    ((L1.mulCLM_isPositive (measurable_polCont σ) (abs_polCont_le σ) (polCont_nonneg σ)).mono h))
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- (4.16): `T_σ v = −c + K(σq + (1 − σ)v)`. -/
theorem T_eq (σ : FirmPolicy X) (v : Lp ℝ 1 R.φ) :
    (R.adp hρ).T σ v = -R.c + R.K (L1.mulCLM R.φ (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ) +
      L1.mulCLM R.φ (measurable_polCont σ) (abs_polCont_le σ) v) := by
  change R.rσ hρ σ + R.Kσ σ v = _
  rw [rσ, Kσ, map_add, ContinuousLinearMap.comp_apply, add_assoc]

theorem Kσ_isPositive (σ : FirmPolicy X) : BanachLattice.IsPositiveOp (R.Kσ σ) := fun v hv =>
  R.K_isPositive _ (L1.mulCLM_isPositive (measurable_polCont σ) (abs_polCont_le σ)
    (polCont_nonneg σ) v hv)

theorem Kσ_le_K (σ : FirmPolicy X) (h : Lp ℝ 1 R.φ) (hh : 0 ≤ h) : R.Kσ σ h ≤ R.K h :=
  R.K_isPositive.mono (L1.mulCLM_le_self (measurable_polCont σ) (abs_polCont_le σ)
    (polCont_le_one σ) hh)

theorem isAdditive : BanachLattice.IsAdditive id (R.adp hρ) (R.rσ hρ) R.Kσ :=
  ⟨R.Kσ_isPositive, fun _ _ => rfl⟩

include hρ in
theorem isDiscountOperator : BanachLattice.IsDiscountOperator (R.K : Lp ℝ 1 R.φ → Lp ℝ 1 R.φ) :=
  BanachLattice.example_4_1_1 R.K_isPositive hρ

theorem isGloballyStable : (R.adp hρ).IsGloballyStable := fun σ =>
  (BanachLattice.theorem_4_1_4 (isIsoOrderEmbedding_id_L1 R.φ) ⟨R.isDiscountOperator hρ,
    fun v w => ((R.isAdditive hρ).abs_sub σ v w).trans (R.Kσ_le_K σ _ (abs_nonneg _))⟩).1

/-- `T_σⁿ 0 = ∑_{t < n} K_σᵗ r_σ`. -/
theorem iterate_T_zero (σ : FirmPolicy X) (n : ℕ) :
    ((R.adp hρ).T σ)^[n] 0 = ∑ t ∈ Finset.range n, (R.Kσ σ ^ t) (R.rσ hρ σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', ih, Finset.sum_range_succ']
    change R.rσ hρ σ + R.Kσ σ (∑ t ∈ Finset.range n, (R.Kσ σ ^ t) (R.rσ hρ σ)) = _
    rw [map_sum, add_comm]
    simp only [pow_succ', pow_zero]
    rfl

/-- **Exercise 4.2.2** (p. 139): `(L¹(φ), 𝕋_RO)` is well-posed, and the lifetime value of `σ` is
`v_σ = (I − K_σ)⁻¹(−c + K(σq)) = ∑ₜ K_σᵗ(−c + K(σq))`, the infinite sum being the limit of its
partial sums. -/
theorem exercise_4_2_2 :
    ∃ hw : (R.adp hρ).WellPosed, ∀ σ, Tendsto
      (fun n => ∑ t ∈ Finset.range n, (R.Kσ σ ^ t) (R.rσ hρ σ)) atTop
      (𝓝 ((R.adp hρ).vσ hw σ)) := by
  refine ⟨(R.isGloballyStable hρ).wellPosed, fun σ => ?_⟩
  have := (R.isGloballyStable hρ).tendsto_vσ σ 0
  simpa only [R.iterate_T_zero hρ] using this

/-- **(4.17) is misprinted.** For the policy that launches everywhere, `K_σ = 0`, so the book's
`v_σ = (I − K_σ)⁻¹(−c + K_σ q)` would be `−c`. But `T_σ(−c) = −c + Kq`, so `−c` is the lifetime
value only when `Kq = 0`. The correct constant term is `−c + K(σq)` (`exercise_4_2_2`). -/
theorem eq_4_17_misprint (σ : FirmPolicy X) (hσ : ∀ x, σ.1 x = true) :
    R.Kσ σ = 0 ∧ ((R.adp hρ).T σ (-R.c + R.Kσ σ (R.q hρ)) = -R.c + R.Kσ σ (R.q hρ) ↔
      R.K (R.q hρ) = 0) := by
  have hcont : L1.mulCLM R.φ (measurable_polCont σ) (abs_polCont_le σ) = 0 :=
    ContinuousLinearMap.ext fun f => Lp.ext (by
      filter_upwards [L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) f,
        Lp.coeFn_zero ℝ 1 R.φ] with x h1 h2
      rw [h1, _root_.zero_apply, h2]
      simp [polCont, hσ x])
  have hind : L1.mulCLM R.φ (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ) = R.q hρ :=
    Lp.ext (by
      filter_upwards [L1.mulCLM_coeFn (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ)] with x h1
      rw [h1]
      simp [polInd, hσ x])
  have hKσ : R.Kσ σ = 0 := by rw [Kσ, hcont, ContinuousLinearMap.comp_zero]
  refine ⟨hKσ, ?_⟩
  rw [hKσ, _root_.zero_apply, add_zero]
  change R.rσ hρ σ + R.Kσ σ (-R.c) = -R.c ↔ _
  rw [hKσ, _root_.zero_apply, add_zero, rσ, hind]
  constructor
  · intro h
    simpa using h
  · intro h
    rw [h, add_zero]

/-- The launch policy `𝟙{q ≥ v}`. -/
noncomputable def launch (v : Lp ℝ 1 R.φ) : FirmPolicy X :=
  ⟨fun x => decide (v x ≤ R.q hρ x), measurable_to_bool (by
    have : (fun x => decide (v x ≤ R.q hρ x)) ⁻¹' {true} = {x | v x ≤ R.q hρ x} := by
      ext x
      simp
    rw [this]
    exact measurableSet_le (Lp.stronglyMeasurable _).measurable
      (Lp.stronglyMeasurable _).measurable)⟩

/-- `σq + (1 − σ)v` is `q` where `σ` launches and `v` elsewhere. -/
theorem mix_coeFn (σ : FirmPolicy X) (v : Lp ℝ 1 R.φ) :
    ⇑(L1.mulCLM R.φ (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ) +
      L1.mulCLM R.φ (measurable_polCont σ) (abs_polCont_le σ) v) =ᵐ[R.φ]
        fun x => if σ.1 x then R.q hρ x else v x := by
  filter_upwards [Lp.coeFn_add (L1.mulCLM R.φ (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ))
      (L1.mulCLM R.φ (measurable_polCont σ) (abs_polCont_le σ) v),
    L1.mulCLM_coeFn (measurable_polInd σ) (abs_polInd_le σ) (R.q hρ),
    L1.mulCLM_coeFn (measurable_polCont σ) (abs_polCont_le σ) v] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]
  simp only [polInd, polCont]
  split_ifs <;> ring

/-- For the launch policy, `σq + (1 − σ)v = q ∨ v`. -/
theorem mix_launch (v : Lp ℝ 1 R.φ) :
    L1.mulCLM R.φ (measurable_polInd (R.launch hρ v)) (abs_polInd_le _) (R.q hρ) +
      L1.mulCLM R.φ (measurable_polCont (R.launch hρ v)) (abs_polCont_le _) v = R.q hρ ⊔ v :=
  Lp.ext (by
    filter_upwards [R.mix_coeFn hρ (R.launch hρ v) v, Lp.coeFn_sup (R.q hρ) v] with x h1 h2
    rw [h1, h2, Pi.sup_apply]
    by_cases h : v x ≤ R.q hρ x
    · simp [launch, h]
    · simp only [launch, h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact (max_eq_right (le_of_not_ge h)).symm)

/-- **Exercise 4.2.3** (p. 139): for `v ∈ L¹(φ)`, the policy `σ = 𝟙{q ≥ v}` is `v`-greedy. -/
theorem exercise_4_2_3 (v : Lp ℝ 1 R.φ) : (R.adp hρ).IsGreedy v (R.launch hρ v) := fun τ => by
  rw [R.T_eq, R.T_eq, R.mix_launch]
  refine add_le_add le_rfl (R.K_isPositive.mono ?_)
  rw [← Lp.coeFn_le]
  filter_upwards [R.mix_coeFn hρ τ v, Lp.coeFn_sup (R.q hρ) v] with x h1 h2
  rw [h1, h2, Pi.sup_apply]
  split_ifs
  · exact le_sup_left
  · exact le_sup_right

theorem adp_regular : (R.adp hρ).Regular := fun v => ⟨_, R.exercise_4_2_3 hρ v⟩

/-- (4.18)–(4.19): the Bellman operator is `Tv = −c + K(q ∨ v)`. -/
theorem adp_bellman (v : Lp ℝ 1 R.φ) : (R.adp hρ).bellman v = -R.c + R.K (R.q hρ ⊔ v) := by
  have heq : (R.adp hρ).bellman v = (R.adp hρ).T (R.launch hρ v) v :=
    le_antisymm (R.exercise_4_2_3 hρ v _) ((R.adp hρ).isGreedy_greedy (R.adp_regular hρ v) _)
  rw [heq, R.T_eq, R.mix_launch]

/-- **Proposition 4.2.3** (p. 140): under Assumptions 4.2.2 and 4.2.3, the fundamental optimality
properties hold for `(L¹(φ), 𝕋_RO)`, VFI converges (geometrically), and OPI and HPI converge. -/
theorem proposition_4_2_3 :
    ∃ hw : (R.adp hρ).WellPosed, (R.adp hρ).FundamentalOptimality hw ∧ ∃ vstar,
      (R.adp hρ).VFIGeometric univ vstar ∧ (R.adp hρ).VFIConverges vstar ∧
        ∀ g, (R.adp hρ).IsSelector g → (R.adp hρ).OPIConverges g vstar ∧
          (R.adp hρ).HPIConverges hw g vstar := by
  have hsr : (R.adp hρ).IsSemiRegular univ :=
    ⟨isClosed_univ, fun v _ => R.adp_regular hρ v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8
    (isIsoOrderEmbedding_id_L1 R.φ) (R.adp hρ) (R.isAdditive hρ) (R.isDiscountOperator hρ)
    R.Kσ_le_K hsr univ_nonempty
  obtain ⟨w, -, -, -, hwG, hwb⟩ := hFO.exists_vstar
  obtain ⟨-, w', hw', hvfi, -⟩ := ADP.theorem_3_1_2 (R.adp_regular hρ) (R.isGloballyStable hρ)
    (((R.adp hρ).solvesBellman_iff hwG).1 hwb)
  obtain rfl : vstar = w' := hgeo.1.unique hw'
  exact ⟨hw, hFO, vstar, hgeo, hvfi, hconv (R.adp_regular hρ)⟩

end RealOption

end SargentStachurski.ADPsOnBanachSpace
