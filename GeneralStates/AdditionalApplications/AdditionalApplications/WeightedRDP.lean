/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.BoundedRDP

/-!
# Weighted contractions

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §7.2.2 (pp. 220–223), with the weighted
supremum norm spaces of §A.5.3.5 (pp. 382–383).

* Weighted spaces (§A.5.3.5): for a weight function `ℓ ≥ 1`, `v ↦ v / ℓ` maps `bℓX` onto `bX`,
  preserving the order and carrying `‖·‖ℓ` to the supremum norm (`norm_eq_wnorm`). So `bℓX` is a
  Banach lattice (Theorem A.5.24) and `ℓ` is a normalized order unit (Exercise A.5.25): both are
  transported from `bX` and `𝟙`. The value space `bℓX₊` is represented by the closed cone `bX₊`
  through `v = ℓh` (`wev`), with `bℓcX₊` the continuous `h` when `ℓ` is continuous.
  **Exercises A.5.22** and **A.5.24** are proved.
* §7.2.2.1: a nonnegative aggregator on `bℓX₊`, measurable and monotone, with (U2)
  `B(x, a, v) ≤ M + Nℓ(x)`. **Lemma 7.2.3**: `(Γ, bℓX₊, B)` is an RDP (`WRDP.toRDP`).
* (U1): `B(x, a, v + κℓ) ≤ B(x, a, v) + λκℓ(x)`, `λ ∈ [0, 1)`.
* **Proposition 7.2.4** (finite actions) and **Proposition 7.2.5** (continuous case), by
  Theorem 4.1.3 with `E = bX` (`= bℓX`), `e = 𝟙` (`= ℓ`) and `V = bX₊` (`= bℓX₊`).
-/

open Set Function Filter Topology MeasureTheory

namespace SargentStachurski.AdditionalApplications

attribute [local instance] BM.normedAddCommGroup BM.module BM.normedSpace BM.lattice
  BM.isOrderedAddMonoid BM.hasSolidNorm BM.completeSpace BM.posSMulMono

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-! ### Weighted supremum norm spaces -/

/-- The `ℓ`-weighted supremum norm `‖v‖ℓ = sup_x |v(x)| / ℓ(x)` (§A.5.3.5). -/
noncomputable def wnorm (ℓ : X → ℝ) (v : X → ℝ) : ℝ := ⨆ x, |v x| / ℓ x

/-- `bℓX`: measurable `v` with `‖v‖ℓ < ∞`, i.e. `|v| ≤ Cℓ` (§A.5.3.5). -/
def bl (ℓ : X → ℝ) : Set (X → ℝ) := {v | Measurable v ∧ ∃ C, ∀ x, |v x| ≤ C * ℓ x}

/-- `bℓX₊`: the nonnegative functions in `bℓX`. -/
def blPlus (ℓ : X → ℝ) : Set (X → ℝ) :=
  {v | Measurable v ∧ (∀ x, 0 ≤ v x) ∧ ∃ C, ∀ x, v x ≤ C * ℓ x}

/-- The weighted function `x ↦ ℓ(x)h(x)` of `h ∈ bX`. -/
def wevB (ℓ : X → ℝ) (h : BM X) : X → ℝ := fun x => ℓ x * h.toFun x

theorem wevB_mem {ℓ : X → ℝ} (hℓm : Measurable ℓ) (hℓ1 : ∀ x, 1 ≤ ℓ x) (h : BM X) :
    wevB ℓ h ∈ bl ℓ := by
  refine ⟨hℓm.mul h.measurable', ‖h‖, fun x => ?_⟩
  rw [wevB, abs_mul, abs_of_pos (zero_lt_one.trans_le (hℓ1 x)), mul_comm ‖h‖]
  exact mul_le_mul_of_nonneg_left (BM.abs_le_norm h x) (zero_lt_one.trans_le (hℓ1 x)).le

/-- The weighted norm of `ℓh` is the supremum norm of `h`: `v ↦ v / ℓ` is an isometry of `bℓX`
onto `bX`, so `bℓX` is a Banach lattice (Theorem A.5.24). -/
theorem norm_eq_wnorm {ℓ : X → ℝ} (hℓ1 : ∀ x, 1 ≤ ℓ x) (h : BM X) :
    ‖h‖ = wnorm ℓ (wevB ℓ h) := by
  rw [BM.norm_def, BM.supNorm, wnorm]
  refine congrArg iSup (funext fun x => ?_)
  have hpos : 0 < ℓ x := zero_lt_one.trans_le (hℓ1 x)
  rw [wevB, abs_mul, abs_of_pos hpos, mul_div_cancel_left₀ _ hpos.ne']

/-- **Exercise A.5.22** (p. 383): `bX ⊆ bℓX`. -/
theorem exercise_A_5_22 {ℓ : X → ℝ} (hℓ1 : ∀ x, 1 ≤ ℓ x) (v : BM X) : v.toFun ∈ bl ℓ :=
  ⟨v.measurable', ‖v‖, fun x => (BM.abs_le_norm v x).trans
    (le_mul_of_one_le_right (norm_nonneg _) (hℓ1 x))⟩

/-- **Exercise A.5.24** (p. 383): convergence in `bℓX` implies pointwise convergence. -/
theorem exercise_A_5_24 {ℓ : X → ℝ} {hs : ℕ → BM X} {h : BM X}
    (hlim : Tendsto hs atTop (𝓝 h)) (x : X) :
    Tendsto (fun n => wevB ℓ (hs n) x) atTop (𝓝 (wevB ℓ h x)) :=
  ((BM.tendstoUniformly_of_tendsto hlim).tendsto_at x).const_mul (ℓ x)

/-- **Exercise A.5.25** (p. 383): `ℓ = ℓ · 𝟙` corresponds to the normalized order unit `𝟙` of
`bX`. -/
theorem exercise_A_5_25 [Nonempty X] (ℓ : X → ℝ) :
    wevB ℓ (BM.const 1) = ℓ ∧ BanachLattice.IsNormalizedOrderUnit (BM.const 1 : BM X) :=
  ⟨funext fun _ => mul_one _, BM.isNormalizedOrderUnit_one⟩

/-- The cone `bX₊`. -/
def posCone (X : Type*) [MeasurableSpace X] : Set (BM X) := {h | 0 ≤ h}

theorem isClosed_posCone : IsClosed (posCone X) := by
  refine isSeqClosed_iff_isClosed.1 fun hs h hhs hlim => ?_
  have hu := BM.tendstoUniformly_of_tendsto hlim
  exact BM.le_def.2 fun x => ge_of_tendsto (hu.tendsto_at x)
    (Eventually.of_forall fun n => BM.le_def.1 (hhs n) x)

theorem add_mem_posCone {h : BM X} (hh : h ∈ posCone X) {κ : ℝ} (hκ : 0 ≤ κ) :
    h + κ • BM.const 1 ∈ posCone X :=
  BM.le_def.2 fun x => by
    have := BM.le_def.1 hh x
    simp only [BM.zero_apply, BM.add_apply, BM.smul_apply, BM.const_apply] at this ⊢
    nlinarith

/-- The value `v = ℓh ∈ bℓX₊` of `h ∈ bX₊`. -/
def wev (ℓ : X → ℝ) (h : posCone X) : X → ℝ := wevB ℓ h.1

theorem wev_mem {ℓ : X → ℝ} (hℓm : Measurable ℓ) (hℓ1 : ∀ x, 1 ≤ ℓ x) (h : posCone X) :
    wev ℓ h ∈ blPlus ℓ := by
  refine ⟨hℓm.mul h.1.measurable', fun x => mul_nonneg (zero_le_one.trans (hℓ1 x))
    (BM.le_def.1 h.2 x), ‖h.1‖, fun x => ?_⟩
  rw [wev, wevB, mul_comm ‖h.1‖]
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (BM.abs_le_norm h.1 x))
    (zero_le_one.trans (hℓ1 x))

/-- `v / ℓ ∈ bX₊` for `v ∈ bℓX₊`. -/
noncomputable def ofBl {ℓ : X → ℝ} (hℓm : Measurable ℓ) (hℓ1 : ∀ x, 1 ≤ ℓ x) {v : X → ℝ}
    (hv : v ∈ blPlus ℓ) : posCone X :=
  ⟨⟨fun x => v x / ℓ x, hv.1.div hℓm, by
    obtain ⟨C, hC⟩ := hv.2.2
    refine ⟨C, fun x => ?_⟩
    have hpos : 0 < ℓ x := zero_lt_one.trans_le (hℓ1 x)
    rw [abs_of_nonneg (div_nonneg (hv.2.1 x) hpos.le), div_le_iff₀ hpos]
    exact hC x⟩,
    BM.le_def.2 fun x => div_nonneg (hv.2.1 x) (zero_le_one.trans (hℓ1 x))⟩

theorem wev_ofBl {ℓ : X → ℝ} (hℓm : Measurable ℓ) (hℓ1 : ∀ x, 1 ≤ ℓ x) {v : X → ℝ}
    (hv : v ∈ blPlus ℓ) : wev ℓ (ofBl hℓm hℓ1 hv) = v :=
  funext fun x => mul_div_cancel₀ _ (zero_lt_one.trans_le (hℓ1 x)).ne'

theorem wev_le_iff {ℓ : X → ℝ} (hℓ1 : ∀ x, 1 ≤ ℓ x) (h h' : posCone X) :
    h ≤ h' ↔ wev ℓ h ≤ wev ℓ h' := by
  change (∀ x, h.1.toFun x ≤ h'.1.toFun x) ↔ ∀ x, ℓ x * h.1.toFun x ≤ ℓ x * h'.1.toFun x
  exact forall_congr' fun x => (mul_le_mul_iff_of_pos_left (zero_lt_one.trans_le (hℓ1 x))).symm

/-- `bℓcX₊` inside `bℓX₊`: the `h` with `ℓh` continuous, i.e. `h` continuous when `ℓ` is. -/
def bcPlus (X : Type*) [MeasurableSpace X] [TopologicalSpace X] : Set (posCone X) :=
  {h | Continuous h.1.toFun}

theorem isClosed_bcPlus [TopologicalSpace X] : IsClosed (bcPlus X) :=
  LDP.isClosed_bc.preimage continuous_subtype_val

theorem zero_mem_bcPlus [TopologicalSpace X] :
    (⟨0, BM.le_def.2 fun _ => le_rfl⟩ : posCone X) ∈ bcPlus X :=
  continuous_const

/-! ### The weighted RDP framework -/

/-- The framework of §7.2.2.1 with condition (U2): a weight function `ℓ ≥ 1`, value space
`bℓX₊`, and an aggregator that is measurable, nonnegative and monotone on `bℓX₊`, with
`B(x, a, v) ≤ M + Nℓ(x)` on `G` for each `v`. -/
structure WRDP (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- the weight function -/
  ℓ : X → ℝ
  measurable_ℓ : Measurable ℓ
  one_le_ℓ : ∀ x, 1 ≤ ℓ x
  /-- the feasible correspondence -/
  Γ : X → Set A
  /-- the aggregator -/
  B : X → A → (X → ℝ) → ℝ
  /-- `(x, a) ↦ B(x, a, v)` is measurable -/
  measurable : ∀ v ∈ blPlus ℓ, Measurable fun p : X × A => B p.1 p.2 v
  /-- `B` is nonnegative on `G` -/
  nonneg : ∀ x, ∀ a ∈ Γ x, ∀ v ∈ blPlus ℓ, 0 ≤ B x a v
  /-- `B` is monotone in `v` on `G` -/
  mono : ∀ x, ∀ a ∈ Γ x, ∀ v ∈ blPlus ℓ, ∀ w ∈ blPlus ℓ, v ≤ w → B x a v ≤ B x a w
  /-- (U2) -/
  U2 : ∀ v ∈ blPlus ℓ, ∃ M N : ℝ, 0 ≤ M ∧ 0 ≤ N ∧ ∀ x, ∀ a ∈ Γ x, B x a v ≤ M + N * ℓ x
  /-- a feasible policy exists -/
  exists_policy : ∃ σ : X → A, Measurable σ ∧ ∀ x, σ x ∈ Γ x

namespace WRDP

variable (M : WRDP X A)

/-- **Lemma 7.2.3** (p. 221): `(Γ, bℓX₊, B)` is an RDP. -/
noncomputable def toRDP : RDP X A (posCone X) where
  ev := wev M.ℓ
  ev_le_iff := wev_le_iff M.one_le_ℓ
  Γ := M.Γ
  B := M.B
  mono x a ha v w hvw := M.mono x a ha _ (wev_mem M.measurable_ℓ M.one_le_ℓ v) _
    (wev_mem M.measurable_ℓ M.one_le_ℓ w) ((wev_le_iff M.one_le_ℓ v w).1 hvw)
  consistent σ hσ hσΓ v := by
    have hv := wev_mem M.measurable_ℓ M.one_le_ℓ v
    obtain ⟨K, N, hK, hN, hKN⟩ := M.U2 _ hv
    have hm : (fun x => M.B x (σ x) (wev M.ℓ v)) ∈ blPlus M.ℓ :=
      ⟨(M.measurable _ hv).comp (measurable_id.prodMk hσ),
        fun x => M.nonneg x _ (hσΓ x) _ hv, K + N, fun x => by
          have h1 := hKN x _ (hσΓ x)
          have h2 := M.one_le_ℓ x
          nlinarith⟩
    exact ⟨ofBl M.measurable_ℓ M.one_le_ℓ hm, wev_ofBl _ _ hm⟩
  exists_policy := M.exists_policy

theorem toRDP_T_apply (σ : M.toRDP.Policy) (h : posCone X) (x : X) :
    M.ℓ x * (M.toRDP.adp.T σ h).1.toFun x = M.B x (σ.1 x) (wev M.ℓ h) :=
  M.toRDP.ev_adp_T σ h x

/-- Condition (U1): `B(x, a, v + κℓ) ≤ B(x, a, v) + λκℓ(x)` on `G` for `v ∈ bℓX₊`, `κ ≥ 0`. -/
def IsBlackwell (lam : ℝ) : Prop :=
  ∀ x, ∀ a ∈ M.Γ x, ∀ v ∈ blPlus M.ℓ, ∀ κ : ℝ, 0 ≤ κ →
    M.B x a (fun y => v y + κ * M.ℓ y) ≤ M.B x a v + lam * κ * M.ℓ x

/-- (U1) gives Blackwell's condition (4.4) for the policy operators on `bX₊` with `e = 𝟙`. -/
theorem T_blackwell {lam : ℝ} (hB : M.IsBlackwell lam) (σ : M.toRDP.Policy) (h : posCone X)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ((M.toRDP.adp.T σ ⟨h.1 + κ • BM.const 1, add_mem_posCone h.2 hκ⟩ : posCone X) : BM X) ≤
      (M.toRDP.adp.T σ h : BM X) + (lam * κ) • BM.const 1 := by
  refine BM.le_def.2 fun x => ?_
  have hpos : 0 < M.ℓ x := zero_lt_one.trans_le (M.one_le_ℓ x)
  have hw : wev M.ℓ ⟨h.1 + κ • BM.const 1, add_mem_posCone h.2 hκ⟩ =
      fun y => wev M.ℓ h y + κ * M.ℓ y := funext fun y => by
    simp only [wev, wevB, BM.add_apply, BM.smul_apply, BM.const_apply]
    ring
  refine le_of_mul_le_mul_left ?_ hpos
  rw [M.toRDP_T_apply, hw]
  simp only [BM.add_apply, BM.smul_apply, BM.const_apply]
  calc M.B x (σ.1 x) (fun y => wev M.ℓ h y + κ * M.ℓ y)
      ≤ M.B x (σ.1 x) (wev M.ℓ h) + lam * κ * M.ℓ x :=
        hB x _ (σ.2.2 x) _ (wev_mem M.measurable_ℓ M.one_le_ℓ h) κ hκ
    _ = M.ℓ x * ((M.toRDP.adp.T σ h).1.toFun x + lam * κ * 1) := by
        rw [mul_add, M.toRDP_T_apply]
        ring

/-- With finitely many actions and measurable sections `{x | a ∈ Γ(x)}`, the RDP is regular
(Lemma 7.1.1). -/
theorem regular_of_finite [Finite A] (hΓ : ∀ a, MeasurableSet {x | a ∈ M.Γ x}) :
    M.toRDP.adp.Regular := fun h =>
  (M.toRDP.lemma_7_1_1 hΓ h fun _ =>
    (M.measurable _ (wev_mem M.measurable_ℓ M.one_le_ℓ h)).comp
      (measurable_id.prodMk measurable_const)).2.1

/-- **Proposition 7.2.4** (p. 222): under (U1)–(U2), with `A` finite (and measurable sections
`{x | a ∈ Γ(x)}`), (i) the fundamental optimality properties hold, (ii) VFI converges
geometrically on `V = bℓX₊`, and (iii) OPI and HPI converge. -/
theorem proposition_7_2_4 [Nonempty X] [Finite A] (hΓ : ∀ a, MeasurableSet {x | a ∈ M.Γ x})
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hB : M.IsBlackwell lam) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar, M.toRDP.adp.VFIGeometric univ vstar ∧
        ∀ g, M.toRDP.adp.IsSelector g →
          M.toRDP.adp.OPIConverges g vstar ∧ M.toRDP.adp.HPIConverges hw g vstar := by
  have hr := M.regular_of_finite hΓ
  have : Nonempty (posCone X) := ⟨⟨0, BM.le_def.2 fun _ => le_rfl⟩⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_3
    BM.isNormalizedOrderUnit_one isClosed_posCone (fun _ hv _ hκ => add_mem_posCone hv hκ)
    M.toRDP.adp hlam0 hlam1 (M.T_blackwell hB) ⟨isClosed_univ, fun v _ => hr v, mapsTo_univ _ _⟩
    univ_nonempty
  exact ⟨hw, hFO, vstar, hgeo, hconv hr⟩

/-- **Proposition 7.2.4**, last claim (p. 222): if `X` is also finite, the fundamental optimality
properties hold and HPI reaches `v*` in finitely many steps from every `v ∈ V_U`. -/
theorem proposition_7_2_4_finite [Nonempty X] [Finite X] [Finite A]
    (hΓ : ∀ a, MeasurableSet {x | a ∈ M.Γ x}) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hB : M.IsBlackwell lam) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∀ g, M.toRDP.adp.IsSelector g → ∀ v ∈ M.toRDP.adp.VU,
        ∃ n, M.toRDP.adp.IsValueFunction ((M.toRDP.adp.howard hw g)^[n] v) := by
  have : CompleteSpace (posCone X) := isClosed_posCone.completeSpace_coe
  have hT : ∀ σ v w, dist (M.toRDP.adp.T σ v) (M.toRDP.adp.T σ w) ≤ lam * dist v w :=
    fun σ => BanachLattice.lemma_4_1_2_subtype BM.isNormalizedOrderUnit_one
      (fun _ hv _ hκ => add_mem_posCone hv hκ) (M.toRDP.adp.mono σ) hlam0 (M.T_blackwell hB σ)
  have hgs := ADP.isGloballyStable_of_contraction ⟨⟨0, BM.le_def.2 fun _ => le_rfl⟩⟩ hlam0
    hlam1 hT
  have hfin : M.toRDP.adp.IsFinite := Set.finite_range _
  exact ⟨_, ADP.fundamentalOptimality_of_finite hgs.isOrderStable (M.regular_of_finite hΓ) hfin⟩

variable [TopologicalSpace X] [TopologicalSpace A]

/-- Under Assumption 7.2.6, for `h ∈ bℓcX₊` (`ℓh` continuous) a greedy policy exists, it attains
`max_{a ∈ Γ(x)} B(x, a, ℓh)`, `Th ∈ bℓcX₊`, and `(Tv)(x) = max_{a ∈ Γ(x)} B(x, a, v)`
(Lemma 7.1.2). -/
theorem greedy_of_continuous (hℓc : Continuous M.ℓ) (hΓ : HasMaxSelections M.Γ)
    (hc : ∀ v ∈ blPlus M.ℓ, Continuous v →
      ContinuousOn (fun p : X × A => M.B p.1 p.2 v) {p | p.2 ∈ M.Γ p.1})
    {h : posCone X} (hh : h ∈ bcPlus X) :
    h ∈ M.toRDP.adp.VG ∧ M.toRDP.adp.bellman h ∈ bcPlus X ∧
      (∃ σ, M.toRDP.IsArgmax h σ) ∧
      ∀ x, IsGreatest ((fun a => M.B x a (wev M.ℓ h)) '' M.Γ x)
        (wev M.ℓ (M.toRDP.adp.bellman h) x) := by
  have hcont : Continuous (wev M.ℓ h) := hℓc.mul hh
  obtain ⟨hiff, ⟨σ, hg⟩, hv, hTc, hgr, -⟩ := M.toRDP.lemma_7_1_2 hΓ h
    (hc _ (wev_mem M.measurable_ℓ M.one_le_ℓ h) hcont)
  refine ⟨hv, ?_, ⟨σ, (hiff σ).1 hg⟩, hgr⟩
  have heq : (M.toRDP.adp.bellman h).1.toFun =
      fun x => wev M.ℓ (M.toRDP.adp.bellman h) x / M.ℓ x := funext fun x => by
    rw [wev, wevB, mul_div_cancel_left₀ _ (zero_lt_one.trans_le (M.one_le_ℓ x)).ne']
  change Continuous (M.toRDP.adp.bellman h).1.toFun
  rw [heq]
  exact hTc.div hℓc fun x => (zero_lt_one.trans_le (M.one_le_ℓ x)).ne'

/-- **Proposition 7.2.5** (p. 222): under (U1)–(U2) and Assumption 7.2.6 (`ℓ` continuous, the
maximum theorem for `Γ`, and `B` continuous on `G` for `v ∈ bℓcX₊`), (i) the fundamental optimality
properties hold, (ii) `v* ∈ bℓcX₊` and (iii) VFI converges geometrically on `bℓcX₊`. Under
Assumption 7.2.7 (`B` continuous on `G` for every `v ∈ bℓX₊`), OPI and HPI also converge. -/
theorem proposition_7_2_5 [Nonempty X] (hℓc : Continuous M.ℓ) (hΓ : HasMaxSelections M.Γ)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) (hB : M.IsBlackwell lam)
    (hc : ∀ v ∈ blPlus M.ℓ, Continuous v →
      ContinuousOn (fun p : X × A => M.B p.1 p.2 v) {p | p.2 ∈ M.Γ p.1}) :
    ∃ hw : M.toRDP.adp.WellPosed, M.toRDP.adp.FundamentalOptimality hw ∧
      ∃ vstar ∈ bcPlus X, Continuous (wev M.ℓ vstar) ∧
        M.toRDP.adp.VFIGeometric (bcPlus X) vstar ∧
        ((∀ v ∈ blPlus M.ℓ, ContinuousOn (fun p : X × A => M.B p.1 p.2 v) {p | p.2 ∈ M.Γ p.1}) →
          ∀ g, M.toRDP.adp.IsSelector g →
            M.toRDP.adp.OPIConverges g vstar ∧ M.toRDP.adp.HPIConverges hw g vstar) := by
  have hsr : M.toRDP.adp.IsSemiRegular (bcPlus X) :=
    ⟨isClosed_bcPlus, fun _ hh => (M.greedy_of_continuous hℓc hΓ hc hh).1,
      fun _ hh => (M.greedy_of_continuous hℓc hΓ hc hh).2.1⟩
  have : Nonempty (posCone X) := ⟨⟨0, BM.le_def.2 fun _ => le_rfl⟩⟩
  obtain ⟨hw, hFO, vstar, hv, hgeo, hconv⟩ := BanachLattice.theorem_4_1_3
    BM.isNormalizedOrderUnit_one isClosed_posCone (fun _ hv _ hκ => add_mem_posCone hv hκ)
    M.toRDP.adp hlam0 hlam1 (M.T_blackwell hB) hsr ⟨_, zero_mem_bcPlus⟩
  refine ⟨hw, hFO, vstar, hv, hℓc.mul hv, hgeo, fun hall => hconv fun h => ?_⟩
  obtain ⟨-, ⟨σ, hg⟩, -⟩ := M.toRDP.lemma_7_1_2 hΓ h
    (hall _ (wev_mem M.measurable_ℓ M.one_le_ℓ h))
  exact ⟨σ, hg⟩

end WRDP

end SargentStachurski.AdditionalApplications
