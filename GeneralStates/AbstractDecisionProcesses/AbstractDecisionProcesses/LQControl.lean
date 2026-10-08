/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AbstractDecisionProcesses.LQAlgebra
import AbstractDecisionProcesses.SpectralRadius
import AbstractDecisionProcesses.Minimization

/-!
# LQ control as an ADP

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §2.3.5.3–§2.3.5.8 (pp. 91–95).

A control matrix `F` is *stable* when `ρ(A + BF) < 1`.

* **Exercise 2.3.15**: for stable `F`, `xₜ = (A + BF)ᵗx₀ → 0`.
* **Lemma 2.3.5**: for stable `F`, `T_F` is globally stable on `𝒫` with fixed point
  `P_F = ∑ₜ ((A + BF)ᵗ)ᵀ(FᵀRF + Q)(A + BF)ᵗ` (2.35), and `xᵀP_F x` is the lifetime cost
  `ℓ_F(x) = ∑ₜ xₜᵀ(FᵀRF + Q)xₜ` (2.30).
* The ADP `(𝒫, 𝕋)` with the Loewner order and stable policies (§2.3.5.4) and **Lemma 2.3.6**
  (it is order stable).
* `𝒫_S`, **Lemma 2.3.7** (the control gain of `P ∈ 𝒫_S` is a stable `P`-min-greedy policy),
  **Lemma 2.3.8** (the Bellman min-operator is the Riccati map on `𝒫_S`) and **Lemma 2.3.9**
  (the Riccati equation, the Bellman min-equation and the LQ Bellman equation (2.26) agree).
* §2.3.5.8, given a fixed point `P*` of the Riccati map in `𝒫_S` (Lemma 2.3.4, which the book
  cites from Bertsekas): (a) `P*` is the least element of `𝒫_Σ`, (b) `T P* = P*`, (c) a policy is
  min-optimal iff it is `P*`-min-greedy; hence (2.38) and the optimality of `F(P*)`.
* **Example 2.3.1**: the scalar lifetime cost `c = (F² + 1)∑ (A + BF)^{2t}` (2.31), and with
  `A = B = 1`, `F = −0.6` costs less than `F = −0.9` from every state.
-/

open Matrix Filter Topology Set Function

open scoped MatrixOrder

namespace SargentStachurski.AbstractDecisionProcesses

/-- The positive semidefinite cone `𝒫` (§2.3.5.2). -/
def psdCone (K : Type*) [Fintype K] : Set (Matrix K K ℝ) := {P | P.PosSemidef}

namespace LQProblem

variable {K U : Type*} [Fintype K] [DecidableEq K] [Fintype U] (L : LQProblem K U)

/-- The closed-loop matrix `A + BF`. -/
def closedLoop (F : Matrix U K ℝ) : Matrix K K ℝ := L.A + L.B * F

/-- `F` is a stable control matrix (§2.3.5.3): `ρ(A + BF) < 1`. -/
def IsStable (F : Matrix U K ℝ) : Prop := specRad (L.closedLoop F) < 1

/-- The per-period cost matrix `FᵀRF + Q`. -/
def costMat (F : Matrix U K ℝ) : Matrix K K ℝ := Fᵀ * L.R * F + L.Q

/-- The `t`-th term `((A + BF)ᵗ)ᵀ(FᵀRF + Q)(A + BF)ᵗ` of (2.35). -/
def discCost (F : Matrix U K ℝ) (t : ℕ) : Matrix K K ℝ :=
  (L.closedLoop F ^ t)ᵀ * L.costMat F * L.closedLoop F ^ t

omit [DecidableEq K] in
/-- `T_F(P) = (FᵀRF + Q) + (A + BF)ᵀP(A + BF)`. -/
theorem TF_eq (F : Matrix U K ℝ) (P : Matrix K K ℝ) :
    L.TF F P = L.costMat F + (L.closedLoop F)ᵀ * P * L.closedLoop F := by
  simp only [TF, costMat, closedLoop]
  abel

/-! ### Exercise 2.3.15 and the decay of `(A + BF)ᵗ` -/

variable {L}

/-- For stable `F`, the entries of `(A + BF)ᵗ` decay geometrically. -/
theorem IsStable.entry_decay [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) :
    ∃ r, 0 ≤ r ∧ r < 1 ∧ ∀ᶠ t in atTop, ∀ i j, |(L.closedLoop F ^ t) i j| ≤ r ^ t := by
  set r := (specRad (L.closedLoop F) + 1) / 2
  have h0 := specRad_nonneg (L.closedLoop F)
  refine ⟨r, by positivity, by unfold IsStable at hF; simp only [r]; linarith, ?_⟩
  have hr : specRad (L.closedLoop F) < r := by unfold IsStable at hF; simp only [r]; linarith
  simp only [eventually_all]
  exact fun i j => eventually_abs_entry_pow_le _ hr i j

/-- For stable `F`, every entry of `(A + BF)ᵗ` tends to zero. -/
theorem IsStable.tendsto_entry [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) (i j : K) :
    Tendsto (fun t => (L.closedLoop F ^ t) i j) atTop (𝓝 0) := by
  obtain ⟨r, hr0, hr1, hev⟩ := hF.entry_decay
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) (hev.mono fun t ht => ht i j)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)

/-- **Exercise 2.3.15** (p. 92): for a stable control matrix, `xₜ = (A + BF)ᵗx₀ → 0`. -/
theorem IsStable.tendsto_state [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F)
    (x₀ : K → ℝ) : Tendsto (fun t => (L.closedLoop F ^ t) *ᵥ x₀) atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro i
  simp only [mulVec, dotProduct, Pi.zero_apply]
  rw [show (0 : ℝ) = ∑ j, 0 * x₀ j by simp]
  exact tendsto_finsetSum _ fun j _ => (hF.tendsto_entry i j).mul_const _

/-! ### Lemma 2.3.5 -/

omit [DecidableEq K] in
/-- `Nᵀ P N` in coordinates. -/
theorem transpose_mul_mul_apply (N P : Matrix K K ℝ) (a b : K) :
    (Nᵀ * P * N) a b = ∑ i, ∑ j, N i a * P i j * N j b := by
  simp only [mul_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq K] in
/-- If the entries of `Nₙ` tend to zero, so do those of `NₙᵀPNₙ`. -/
theorem tendsto_transpose_mul_mul_zero {N : ℕ → Matrix K K ℝ}
    (hN : ∀ i j, Tendsto (fun n => N n i j) atTop (𝓝 0)) (P : Matrix K K ℝ) (a b : K) :
    Tendsto (fun n => ((N n)ᵀ * P * N n) a b) atTop (𝓝 0) := by
  simp only [transpose_mul_mul_apply]
  rw [show (0 : ℝ) = ∑ i : K, ∑ j : K, 0 * P i j * 0 by simp]
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    ((hN i a).mul_const _).mul (hN j b)

/-- The iterates of `T_F`: `T_Fⁿ P = ∑_{t<n} (Mᵗ)ᵀCMᵗ + (Mⁿ)ᵀPMⁿ` with `M = A + BF`,
`C = FᵀRF + Q`. -/
theorem TF_iterate (F : Matrix U K ℝ) (P : Matrix K K ℝ) (n : ℕ) :
    (L.TF F)^[n] P = ∑ t ∈ Finset.range n, L.discCost F t +
      (L.closedLoop F ^ n)ᵀ * P * L.closedLoop F ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [discCost] at ih ⊢
    rw [iterate_succ_apply', ih, TF_eq, Finset.sum_range_succ', pow_zero, transpose_one,
      Matrix.one_mul, Matrix.mul_one, pow_succ, transpose_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul, pow_succ,
      transpose_mul, Matrix.mul_assoc]
    abel

variable (L) in
/-- The lifetime cost matrix (2.35): `P_F = ∑ₜ ((A + BF)ᵗ)ᵀ(FᵀRF + Q)(A + BF)ᵗ`. -/
noncomputable def PF (F : Matrix U K ℝ) : Matrix K K ℝ :=
  Matrix.of fun a b => ∑' t : ℕ, L.discCost F t a b

/-- (2.35): the series defining `P_F` converges, entry by entry. -/
theorem IsStable.hasSum_PF [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) (a b : K) :
    HasSum (fun t => L.discCost F t a b)
      (L.PF F a b) := by
  obtain ⟨r, hr0, hr1, hev⟩ := hF.entry_decay
  set c := ∑ i : K, ∑ j : K, |L.costMat F i j|
  have hsum : Summable fun t => L.discCost F t a b := by
    refine Summable.of_norm_bounded_eventually (g := fun t : ℕ => c * (r ^ 2) ^ t)
      ((summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left c) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hev] with t ht
    rw [Real.norm_eq_abs, discCost, transpose_mul_mul_apply]
    calc |∑ i, ∑ j, (L.closedLoop F ^ t) i a * L.costMat F i j * (L.closedLoop F ^ t) j b|
        ≤ ∑ i, ∑ j, |(L.closedLoop F ^ t) i a * L.costMat F i j * (L.closedLoop F ^ t) j b| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ j, r ^ t * |L.costMat F i j| * r ^ t := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul_of_nonneg_right (ht i a) (abs_nonneg _)) (ht j b)
              (abs_nonneg _) (by positivity)
      _ = c * (r ^ 2) ^ t := by
          simp only [c, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
  exact hsum.hasSum

/-- **Lemma 2.3.5** (p. 93), convergence: for stable `F`, `T_Fⁿ P → P_F` entrywise from every
`P`. -/
theorem IsStable.tendsto_TF_iterate [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F)
    (P : Matrix K K ℝ) (a b : K) :
    Tendsto (fun n => ((L.TF F)^[n] P) a b) atTop (𝓝 (L.PF F a b)) := by
  simp only [TF_iterate, Matrix.add_apply, Matrix.sum_apply]
  rw [← add_zero (L.PF F a b)]
  exact (hF.hasSum_PF a b).tendsto_sum_nat.add
    (tendsto_transpose_mul_mul_zero (hF.tendsto_entry) P a b)

omit [DecidableEq K] in
/-- `T_F` is continuous, entry by entry. -/
theorem tendsto_TF {F : Matrix U K ℝ} {Pn : ℕ → Matrix K K ℝ} {P : Matrix K K ℝ}
    (h : ∀ i j, Tendsto (fun n => Pn n i j) atTop (𝓝 (P i j))) (a b : K) :
    Tendsto (fun n => L.TF F (Pn n) a b) atTop (𝓝 (L.TF F P a b)) := by
  simp only [TF_eq, Matrix.add_apply, transpose_mul_mul_apply]
  exact tendsto_const_nhds.add (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    ((h i j).const_mul _).mul_const _)

/-- **Lemma 2.3.5** (p. 93), fixed point: `T_F P_F = P_F`. -/
theorem IsStable.TF_PF [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) :
    L.TF F (L.PF F) = L.PF F := by
  ext a b
  have h1 := (hF.tendsto_TF_iterate 0 a b).comp (tendsto_add_atTop_nat 1)
  have h2 := L.tendsto_TF (F := F) (fun i j => hF.tendsto_TF_iterate 0 i j) a b
  refine tendsto_nhds_unique h2 ?_
  refine h1.congr fun n => ?_
  simp only [Function.comp_apply, iterate_succ_apply']

/-- `P_F` is the only fixed point of `T_F`. -/
theorem IsStable.eq_PF [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) {P : Matrix K K ℝ}
    (hP : L.TF F P = P) : P = L.PF F := by
  ext a b
  have : ∀ n, (L.TF F)^[n] P = P := fun n => iterate_fixed hP n
  exact tendsto_nhds_unique (by simp [this])
    (hF.tendsto_TF_iterate P a b)

/-- `P_F` is positive semidefinite: it is a limit of positive semidefinite partial sums. -/
theorem IsStable.PF_posSemidef [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) :
    (L.PF F).PosSemidef := by
  have hC : (L.costMat F).PosSemidef :=
    (posSemidef_transpose_mul_mul L.R_pd.posSemidef F).add L.Q_psd
  have hmem : ∀ n, ((L.TF F)^[n] 0).PosSemidef := by
    intro n
    induction n with
    | zero => exact PosSemidef.zero
    | succ n ih => rw [iterate_succ_apply']; exact L.TF_posSemidef F ih
  have hlim : Tendsto (fun n => (L.TF F)^[n] 0) atTop (𝓝 (L.PF F)) :=
    tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hF.tendsto_TF_iterate 0 a b
  exact posSemidef_is_closed.mem_of_tendsto hlim (Eventually.of_forall hmem)

variable (L) in
/-- `T_F` restricted to the positive semidefinite cone `𝒫`. -/
def TFpsd (F : Matrix U K ℝ) (P : ↥(psdCone K)) : ↥(psdCone K) :=
  ⟨L.TF F P, L.TF_posSemidef F P.2⟩

omit [DecidableEq K] in
theorem TFpsd_iterate (F : Matrix U K ℝ) (P : ↥(psdCone K)) (n : ℕ) :
    ((L.TFpsd F)^[n] P : Matrix K K ℝ) = (L.TF F)^[n] P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih]; rfl

omit [DecidableEq K] in
/-- **Lemma 2.3.5** (p. 93): for stable `F`, `T_F` is globally stable on `𝒫`, with fixed point
`P_F` (2.35). -/
theorem IsStable.globallyStable [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) :
    GloballyStable (L.TFpsd F) := by
  classical
  refine ⟨⟨L.PF F, hF.PF_posSemidef⟩, Subtype.ext hF.TF_PF, fun P hP => Subtype.ext
    (hF.eq_PF (congrArg Subtype.val hP)), fun P => ?_⟩
  rw [tendsto_subtype_rng]
  simp only [TFpsd_iterate]
  exact tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hF.tendsto_TF_iterate P a b

/-- (2.30) and (2.35) (p. 93): `xᵀP_F x = ℓ_F(x) = ∑ₜ xₜᵀ(FᵀRF + Q)xₜ` with `xₜ = (A + BF)ᵗx`. -/
theorem IsStable.hasSum_cost [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) (x : K → ℝ) :
    HasSum (fun t => ((L.closedLoop F ^ t) *ᵥ x) ⬝ᵥ (L.costMat F *ᵥ ((L.closedLoop F ^ t) *ᵥ x)))
      (x ⬝ᵥ (L.PF F *ᵥ x)) := by
  have e : ∀ t, ((L.closedLoop F ^ t) *ᵥ x) ⬝ᵥ (L.costMat F *ᵥ ((L.closedLoop F ^ t) *ᵥ x)) =
      x ⬝ᵥ (L.discCost F t *ᵥ x) := fun t => (dotProduct_transpose_mul_mul _ _ x).symm
  simp_rw [e]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact hasSum_sum fun a _ => hasSum_sum fun b _ =>
    ((hF.hasSum_PF a b).mul_right (x b)).mul_left (x a)

/-! ### The ADP `(𝒫, 𝕋)` -/

variable (L) in
/-- The stable control matrices, the policies of §2.3.5.4. -/
def StablePolicy : Type _ := {F : Matrix U K ℝ // L.IsStable F}

/-- The LQ ADP `(𝒫, 𝕋)` (§2.3.5.4) with the Loewner order, given that some stable control matrix
exists (otherwise `𝕋` would be empty). **Exercise 2.3.16** gives monotonicity. -/
noncomputable def adp (hne : ∃ F, L.IsStable F) : ADP ↥(psdCone K) (StablePolicy L) where
  T F := L.TFpsd F.1
  mono F _ _ h := L.TF_mono F.1 h
  nonempty := ⟨⟨_, hne.choose_spec⟩⟩

omit [DecidableEq K] in
/-- **Lemma 2.3.6** (p. 93): the LQ ADP is (strongly) order stable. -/
theorem adp_isStronglyOrderStable [Nonempty K] (hne : ∃ F, L.IsStable F) :
    (adp hne).IsStronglyOrderStable := fun F =>
  stronglyOrderStable_of_globallyStable ((adp hne).mono F) F.2.globallyStable

/-! ### Min-greedy policies and the Bellman min-equation -/

omit [DecidableEq K] in
/-- Symmetric matrices with the same quadratic form are equal. -/
theorem eq_of_dotProduct_mulVec_eq {S S' : Matrix K K ℝ} (hS : Sᵀ = S) (hS' : S'ᵀ = S')
    (h : ∀ x, x ⬝ᵥ (S *ᵥ x) = x ⬝ᵥ (S' *ᵥ x)) : S = S' := by
  classical
  set D := S - S'
  have hD : Dᵀ = D := by simp only [D, transpose_sub, hS, hS']
  have h0 : ∀ x, x ⬝ᵥ (D *ᵥ x) = 0 := fun x => by
    simp only [D, sub_mulVec, dotProduct_sub, h x, sub_self]
  have hentry : ∀ i j, Pi.single i 1 ⬝ᵥ (D *ᵥ Pi.single j 1) = D i j := fun i j => by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [← sub_eq_zero]
  ext i j
  have hii := h0 (Pi.single i 1)
  have hjj := h0 (Pi.single j 1)
  have hij := h0 (Pi.single i 1 + Pi.single j 1)
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hentry, hentry, hentry,
    hentry] at hij
  rw [hentry] at hii hjj
  have hsym : D j i = D i j := by
    have := congrFun (congrFun hD i) j
    rwa [transpose_apply] at this
  change D i j = 0
  linarith

variable [DecidableEq U]

variable (L) in
/-- `𝒫_S`: the positive semidefinite `P` whose control gain `F(P)` is stable (§2.3.5.6). -/
def PS : Set (Matrix K K ℝ) := {P | P.PosSemidef ∧ L.IsStable (L.gain P)}

omit [DecidableEq K] in
/-- **Lemma 2.3.7** (p. 94): for `P ∈ 𝒫_S`, the control gain `F(P)` is a stable `P`-min-greedy
policy. -/
theorem gain_isMinGreedy (hne : ∃ F, L.IsStable F) {P : Matrix K K ℝ} (hP : P ∈ L.PS) :
    (adp hne).IsMinGreedy ⟨P, hP.1⟩ ⟨L.gain P, hP.2⟩ :=
  fun G => (L.gain_iff_TF_le hP.1 _).1 rfl G.1

omit [DecidableEq K] in
/-- **Lemma 2.3.8** (p. 94): on `𝒫_S` the Bellman min-operator is the Riccati map. -/
theorem isMinBellmanValue_riccati (hne : ∃ F, L.IsStable F) {P : Matrix K K ℝ} (hP : P ∈ L.PS) :
    (adp hne).IsMinBellmanValue ⟨P, hP.1⟩ ⟨L.riccati P, L.riccati_posSemidef hP.1⟩ := by
  have hT : (adp hne).T ⟨L.gain P, hP.2⟩ ⟨P, hP.1⟩ = ⟨L.riccati P, L.riccati_posSemidef hP.1⟩ :=
    Subtype.ext (L.riccati_eq_TF hP.1).symm
  refine ⟨?_, fun w hw => hT ▸ hw ⟨_, rfl⟩⟩
  rintro _ ⟨G, rfl⟩
  rw [← hT]
  exact gain_isMinGreedy hne hP G

omit [DecidableEq K] in
/-- **Lemma 2.3.9** (p. 95): for `P ∈ 𝒫_S`, (i) `R(P) = P` iff (ii) `T▿P = P` iff (iii)
`ℓ(x) = xᵀPx` satisfies the LQ Bellman equation (2.26),
`ℓ(x) = min_u {xᵀQx + uᵀRu + ℓ(Ax + Bu)}`. -/
theorem riccati_tfae (hne : ∃ F, L.IsStable F) {P : Matrix K K ℝ} (hP : P ∈ L.PS) :
    (L.riccati P = P ↔ (adp hne).SolvesMinBellman ⟨P, hP.1⟩) ∧
      (L.riccati P = P ↔ ∀ x, IsLeast (range (L.cost P x)) (x ⬝ᵥ (P *ᵥ x))) := by
  have h8 := isMinBellmanValue_riccati hne hP
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h x => ?_, fun h => ?_⟩⟩
  · have : (⟨L.riccati P, L.riccati_posSemidef hP.1⟩ : ↥(psdCone K)) = ⟨P, hP.1⟩ :=
      Subtype.ext h
    rw [this] at h8
    exact h8
  · exact congrArg Subtype.val (h8.unique h)
  · have hval : x ⬝ᵥ (P *ᵥ x) = L.cost P x (L.gain P *ᵥ x) := by
      rw [← L.dotProduct_TF, ← L.riccati_eq_TF hP.1, h]
    rw [hval]
    exact ⟨⟨_, rfl⟩, by rintro _ ⟨u, rfl⟩; exact (L.gain_isMinimizer hP.1 x).1 u⟩
  · refine eq_of_dotProduct_mulVec_eq (posSemidef_iff_real.1 (L.riccati_posSemidef hP.1)).1
      (posSemidef_iff_real.1 hP.1).1 fun x => ?_
    rw [L.riccati_eq_TF hP.1, L.dotProduct_TF]
    have hmin : IsLeast (range (L.cost P x)) (L.cost P x (L.gain P *ᵥ x)) :=
      ⟨⟨_, rfl⟩, by rintro _ ⟨u, rfl⟩; exact (L.gain_isMinimizer hP.1 x).1 u⟩
    exact hmin.unique (h x)

omit [DecidableEq K] in
/-- §2.3.5.8 (p. 95): if `P* ∈ 𝒫_S` solves the Riccati equation (as Lemma 2.3.4 provides under
controllability and observability), then (a) `P*` is the least element of `𝒫_Σ`, (b) `P*` solves
the Bellman min-equation, (c) a policy is min-optimal iff it is `P*`-min-greedy, (2.38) holds,
and `F(P*)` is min-optimal. -/
theorem optimality [Nonempty K] (hne : ∃ F, L.IsStable F) {Pstar : Matrix K K ℝ}
    (hPS : Pstar ∈ L.PS) (hfix : L.riccati Pstar = Pstar) :
    IsLeast (adp hne).VSig ⟨Pstar, hPS.1⟩ ∧ (adp hne).SolvesMinBellman ⟨Pstar, hPS.1⟩ ∧
      (∀ F, (adp hne).IsMinOptimal (adp_isStronglyOrderStable hne).isOrderStable.wellPosed F ↔
        (adp hne).IsMinGreedy ⟨Pstar, hPS.1⟩ F) ∧
      (∀ x, IsLeast (range (L.cost Pstar x)) (x ⬝ᵥ (Pstar *ᵥ x))) ∧
      (adp hne).IsMinOptimal (adp_isStronglyOrderStable hne).isOrderStable.wellPosed
        ⟨L.gain Pstar, hPS.2⟩ := by
  have hos := (adp_isStronglyOrderStable hne).isOrderStable
  have hb : (adp hne).SolvesMinBellman ⟨Pstar, hPS.1⟩ := (riccati_tfae hne hPS).1.1 hfix
  have hG : (⟨Pstar, hPS.1⟩ : ↥(psdCone K)) ∈ (adp hne).VGmin :=
    ⟨⟨L.gain Pstar, hPS.2⟩, gain_isMinGreedy hne hPS⟩
  obtain ⟨⟨σ, hσ⟩, ⟨v, hv, -, -, huniq⟩, hbp⟩ := hos.minFundamentalOptimality hG hb
  have hvP : (⟨Pstar, hPS.1⟩ : ↥(psdCone K)) = v := huniq _ hG hb
  have hc : ∀ F, (adp hne).IsMinOptimal hos.wellPosed F ↔
      (adp hne).IsMinGreedy ⟨Pstar, hPS.1⟩ F := fun F => by
    rw [hbp F]
    constructor
    · rintro ⟨w, hw, hg⟩
      rwa [hvP, ← hw.unique hv]
    · intro hg
      exact ⟨v, hv, hvP ▸ hg⟩
  refine ⟨?_, hb, hc, (riccati_tfae hne hPS).2.1 hfix, (hc _).2 (gain_isMinGreedy hne hPS)⟩
  rw [hvP, ← hσ.isGLB.unique hv]
  exact hσ

/-! ### Example 2.3.1 -/

/-- **Example 2.3.1** (p. 91), (2.31): in the scalar case with `Q = R = 1`, a control `F` with
`|A + BF| < 1` has lifetime cost `ℓ_F(x₀) = c x₀²`, `c = (F² + 1)∑ₜ (A + BF)^{2t} =
(F² + 1)/(1 − (A + BF)²)`. -/
theorem scalar_lifetimeCost {A B F : ℝ} (h : |A + B * F| < 1) (x₀ : ℝ) :
    HasSum (fun t : ℕ => ((A + B * F) ^ t * x₀) ^ 2 * (F ^ 2 + 1))
      ((F ^ 2 + 1) / (1 - (A + B * F) ^ 2) * x₀ ^ 2) := by
  have hq0 : 0 ≤ (A + B * F) ^ 2 := sq_nonneg _
  have hq1 : (A + B * F) ^ 2 < 1 := by
    have := (sq_lt_one_iff_abs_lt_one _).2 h
    exact this
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left ((F ^ 2 + 1) * x₀ ^ 2)
  convert hg using 1
  · funext t
    rw [mul_pow, ← pow_mul, mul_comm t 2, pow_mul]
    ring
  · field_simp

/-- **Example 2.3.1** (p. 92): with `A = B = 1`, the control `F = −0.6` has lower lifetime cost
than `F = −0.9` from every state (`c = 34/21 < 181/99`). -/
theorem scalar_compare (x₀ : ℝ) :
    ((-0.6 : ℝ) ^ 2 + 1) / (1 - (1 + 1 * (-0.6)) ^ 2) * x₀ ^ 2 ≤
      ((-0.9 : ℝ) ^ 2 + 1) / (1 - (1 + 1 * (-0.9)) ^ 2) * x₀ ^ 2 := by
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  norm_num

end LQProblem

end SargentStachurski.AbstractDecisionProcesses
