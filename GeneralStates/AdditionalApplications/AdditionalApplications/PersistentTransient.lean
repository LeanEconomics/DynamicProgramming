/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AdditionalApplications.ContinuationValues
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Persistent and transient wage components

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §8.1.3.3 (pp. 257–261).

The persistent state `z` is `P`-Markov on `Z` with stationary distribution `φ`; next period's
offer is `w' = ω(z', ζ')` with `ζ'` drawn iid from `ν`, independent of everything else. The book's
(8.23) is the case `Z = ℝ`, `Z_{t+1} = ρZ_t + d + sε_{t+1}`, `ζ ∼ N(0, 1)` and
`ω(z, ζ) = exp(z) + exp(μ + σζ)`. Continuation values `h ∈ L¹(φ)` satisfy (8.26), and policies
`σ(w', z')` act through

`(T̂_σ h)(z) = c + β 𝔼_z{σ(w', z') w'/(1 − β) + (1 − σ(w', z'))h(z')}` (8.28),

which is `T̂_σ h = c + βP(Φ_σ h)` with `(Φ_σ h)(z') = ∫ [σ e + (1 − σ)h(z')] ν(dζ')`. It is affine,
`T̂_σ h = m_σ + K_σ h` with `0 ≤ K_σ ≤ K = βP`.

* **Exercise 8.1.21**: the policy `σ(w', z') = 𝟙{w'/(1 − β) ≥ h(z')}` is `h`-greedy; hence, by
  Theorem 4.1.8, the fundamental optimality properties hold and VFI, OPI and HPI converge.
* **Exercise 8.1.22**: the Bellman operator is (8.29),
  `(T̂h)(z) = c + β 𝔼_z max{w'/(1 − β), h(z')}`.
* **Exercise 8.1.23**: `T̂` is a contraction of modulus `β` on `L¹(φ)`.
* **Exercise 8.1.24**: the fixed point `h*` is increasing in `c` (almost everywhere).
-/

open Set Function Filter Topology MeasureTheory ProbabilityTheory

namespace SargentStachurski.AdditionalApplications

/-- The job search model with persistent and transient wage components. -/
structure PersistentSearch (Z Ξ : Type*) [MeasurableSpace Z] [MeasurableSpace Ξ] where
  /-- the kernel of the persistent state -/
  P : Kernel Z Z
  [isMarkov : IsMarkovKernel P]
  /-- a stationary distribution of `P` -/
  φ : Measure Z
  [isProb : IsProbabilityMeasure φ]
  stationary : φ.bind P = φ
  /-- the distribution of the transient shock -/
  ν : Measure Ξ
  [isProbν : IsProbabilityMeasure ν]
  /-- the offer `w' = ω(z', ζ')` -/
  ω : Z → Ξ → ℝ
  measurable_ω : Measurable (uncurry ω)
  integrable_ω : Integrable (uncurry ω) (φ.prod ν)
  /-- unemployment compensation -/
  c : ℝ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1

namespace PersistentSearch

attribute [local instance] PersistentSearch.isMarkov PersistentSearch.isProb
  PersistentSearch.isProbν

variable {Z Ξ : Type*} [MeasurableSpace Z] [MeasurableSpace Ξ] (M : PersistentSearch Z Ξ)

/-- The stopping value `e(z', ζ') = ω(z', ζ')/(1 − β)`. -/
noncomputable def e (z : Z) (ζ : Ξ) : ℝ := M.ω z ζ / (1 - M.β)

theorem measurable_e : Measurable (uncurry M.e) := M.measurable_ω.div_const _

theorem integrable_e : Integrable (uncurry M.e) (M.φ.prod M.ν) := M.integrable_ω.div_const _

theorem ae_integrable_e : ∀ᵐ z ∂M.φ, Integrable (M.e z) M.ν := M.integrable_e.prod_right_ae

theorem integrable_absInt : Integrable (fun z => ∫ ζ, |M.e z ζ| ∂M.ν) M.φ := by
  have := M.integrable_e.norm.integral_prod_left
  simpa [Real.norm_eq_abs] using this

/-- The Markov operator `P` on `L¹(φ)`. -/
noncomputable def Pop : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ := L1.markovCLM M.stationary

/-- The constant `c` in `L¹(φ)`. -/
noncomputable def cconst : Lp ℝ 1 M.φ := (memLp_const M.c).toLp _

theorem measurable_pair (σ : StopPolicy (ℝ × Z)) :
    Measurable fun p : Z × Ξ => σ.1 (M.ω p.1 p.2, p.1) :=
  σ.2.comp (M.measurable_ω.prodMk measurable_fst)

/-- `z' ↦ ∫ σ(w', z') e ν(dζ')`. -/
noncomputable def accF (σ : StopPolicy (ℝ × Z)) (z : Z) : ℝ :=
  ∫ ζ, (if σ.1 (M.ω z ζ, z) then M.e z ζ else 0) ∂M.ν

/-- `q_σ(z') = ν{ζ' : σ(w', z') = 0}`, as `∫ (1 − σ) dν`. -/
noncomputable def qF (σ : StopPolicy (ℝ × Z)) (z : Z) : ℝ :=
  ∫ ζ, (if σ.1 (M.ω z ζ, z) then 0 else 1) ∂M.ν

theorem measurable_accF (σ : StopPolicy (ℝ × Z)) : Measurable (M.accF σ) := by
  have hm : Measurable fun p : Z × Ξ => if σ.1 (M.ω p.1 p.2, p.1) then M.e p.1 p.2 else 0 :=
    Measurable.ite ((M.measurable_pair σ) (measurableSet_singleton true)) M.measurable_e
      measurable_const
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := M.ν)).measurable

theorem measurable_qF (σ : StopPolicy (ℝ × Z)) : Measurable (M.qF σ) := by
  have hm : Measurable fun p : Z × Ξ => if σ.1 (M.ω p.1 p.2, p.1) then (0 : ℝ) else 1 :=
    Measurable.ite ((M.measurable_pair σ) (measurableSet_singleton true)) measurable_const
      measurable_const
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := M.ν)).measurable

theorem qF_nonneg (σ : StopPolicy (ℝ × Z)) (z : Z) : 0 ≤ M.qF σ z :=
  integral_nonneg fun ζ => by dsimp only; split_ifs <;> norm_num

theorem qF_le_one (σ : StopPolicy (ℝ × Z)) (z : Z) : M.qF σ z ≤ 1 := by
  calc M.qF σ z ≤ ∫ _, (1 : ℝ) ∂M.ν := integral_mono_of_nonneg
        (Eventually.of_forall fun ζ => by dsimp only; split_ifs <;> norm_num) (integrable_const _)
        (Eventually.of_forall fun ζ => by dsimp only; split_ifs <;> norm_num)
    _ = 1 := by simp

theorem abs_qF_le (σ : StopPolicy (ℝ × Z)) (z : Z) : |M.qF σ z| ≤ 1 := by
  rw [abs_of_nonneg (M.qF_nonneg σ z)]
  exact M.qF_le_one σ z

theorem ae_abs_accF_le (σ : StopPolicy (ℝ × Z)) :
    ∀ᵐ z ∂M.φ, |M.accF σ z| ≤ ∫ ζ, |M.e z ζ| ∂M.ν := by
  filter_upwards [M.ae_integrable_e] with z hi
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => abs_nonneg _) hi.abs (Eventually.of_forall fun ζ => ?_))
  dsimp only
  split_ifs
  · exact le_rfl
  · simp

theorem integrable_accF (σ : StopPolicy (ℝ × Z)) : Integrable (M.accF σ) M.φ :=
  M.integrable_absInt.mono' (M.measurable_accF σ).aestronglyMeasurable
    (by filter_upwards [M.ae_abs_accF_le σ] with z hz; rw [Real.norm_eq_abs]; exact hz)

/-- `accF σ` in `L¹(φ)`. -/
noncomputable def accL (σ : StopPolicy (ℝ × Z)) : Lp ℝ 1 M.φ := (M.integrable_accF σ).toL1 _

/-- `Φ_σ h = ∫ [σe + (1 − σ)h(z')] ν(dζ')`. -/
noncomputable def Φσ (σ : StopPolicy (ℝ × Z)) (h : Lp ℝ 1 M.φ) : Lp ℝ 1 M.φ :=
  M.accL σ + L1.mulCLM M.φ (M.measurable_qF σ) (M.abs_qF_le σ) h

/-- `m_σ = c + βP(accF σ)`. -/
noncomputable def mσ (σ : StopPolicy (ℝ × Z)) : Lp ℝ 1 M.φ := M.cconst + M.β • M.Pop (M.accL σ)

/-- `K_σ h = βP((1 − σ)h)`. -/
noncomputable def Kσ (σ : StopPolicy (ℝ × Z)) : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ :=
  M.β • (M.Pop.comp (L1.mulCLM M.φ (M.measurable_qF σ) (M.abs_qF_le σ)))

/-- `K = βP`. -/
noncomputable def D : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ := M.β • M.Pop

theorem smul_isPositive {A : Lp ℝ 1 M.φ →L[ℝ] Lp ℝ 1 M.φ} (hA : BanachLattice.IsPositiveOp A) :
    BanachLattice.IsPositiveOp (M.β • A) := fun v hv => by
  have h := hA v hv
  rw [← Lp.coeFn_nonneg] at h ⊢
  filter_upwards [Lp.coeFn_smul M.β (A v), h] with x h1 h2
  change 0 ≤ (M.β • A v) x
  rw [h1, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg M.β_nonneg h2

theorem smul_le_smul' {a b : Lp ℝ 1 M.φ} (h : a ≤ b) : M.β • a ≤ M.β • b := by
  rw [← Lp.coeFn_le]
  filter_upwards [Lp.coeFn_smul M.β a, Lp.coeFn_smul M.β b, (Lp.coeFn_le _ _).2 h]
    with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left h3 M.β_nonneg

theorem D_isPositive : BanachLattice.IsPositiveOp M.D :=
  M.smul_isPositive (L1.markovCLM_isPositive M.stationary)

theorem Kσ_isPositive (σ : StopPolicy (ℝ × Z)) : BanachLattice.IsPositiveOp (M.Kσ σ) :=
  M.smul_isPositive fun v hv => L1.markovCLM_isPositive M.stationary _
    (L1.mulCLM_isPositive (M.measurable_qF σ) (M.abs_qF_le σ) (M.qF_nonneg σ) v hv)

theorem Kσ_le_D (σ : StopPolicy (ℝ × Z)) (h : Lp ℝ 1 M.φ) (hh : 0 ≤ h) : M.Kσ σ h ≤ M.D h := by
  change M.β • M.Pop (L1.mulCLM M.φ (M.measurable_qF σ) (M.abs_qF_le σ) h) ≤ M.β • M.Pop h
  exact M.smul_le_smul' ((L1.markovCLM_isPositive M.stationary).mono
    (L1.mulCLM_le_self (M.measurable_qF σ) (M.abs_qF_le σ) (M.qF_le_one σ) hh))

theorem norm_D_le : ‖M.D‖ ≤ M.β :=
  ContinuousLinearMap.opNorm_le_bound _ M.β_nonneg fun v => by
    change ‖M.β • M.Pop v‖ ≤ M.β * ‖v‖
    rw [norm_smul, Real.norm_of_nonneg M.β_nonneg]
    refine mul_le_mul_of_nonneg_left ((M.Pop.le_opNorm v).trans ?_) M.β_nonneg
    exact (mul_le_mul_of_nonneg_right (L1.markovCLM_norm_le M.stationary)
      (norm_nonneg v)).trans_eq (one_mul _)

theorem specRad_D_lt_one : BanachLattice.specRad M.D < 1 :=
  ((BanachLattice.specRad_le_norm _).trans M.norm_D_le).trans_lt M.β_lt_one

/-- The continuation value ADP `(L¹(φ), 𝕋̂)` of (8.28). -/
noncomputable def adp : ADP (Lp ℝ 1 M.φ) (StopPolicy (ℝ × Z)) where
  T σ h := M.mσ σ + M.Kσ σ h
  mono σ _ _ h := add_le_add le_rfl ((M.Kσ_isPositive σ).mono h)
  nonempty := ⟨⟨fun _ => true, measurable_const⟩⟩

/-- (8.28): `T̂_σ h = c + βP(Φ_σ h)`. -/
theorem T_eq (σ : StopPolicy (ℝ × Z)) (h : Lp ℝ 1 M.φ) :
    M.adp.T σ h = M.cconst + M.β • M.Pop (M.Φσ σ h) := by
  change M.cconst + M.β • M.Pop (M.accL σ) +
    M.β • M.Pop (L1.mulCLM M.φ (M.measurable_qF σ) (M.abs_qF_le σ) h) = _
  rw [Φσ, map_add, smul_add, add_assoc]

/-- `Φ_σ h = ∫ [σe + (1 − σ)h(z')] ν(dζ')` almost everywhere. -/
theorem Φσ_coeFn (σ : StopPolicy (ℝ × Z)) (h : Lp ℝ 1 M.φ) :
    ⇑(M.Φσ σ h) =ᵐ[M.φ] fun z => ∫ ζ, (if σ.1 (M.ω z ζ, z) then M.e z ζ else h z) ∂M.ν := by
  filter_upwards [Lp.coeFn_add (M.accL σ) (L1.mulCLM M.φ (M.measurable_qF σ) (M.abs_qF_le σ) h),
    (M.integrable_accF σ).coeFn_toL1,
    L1.mulCLM_coeFn (M.measurable_qF σ) (M.abs_qF_le σ) h, M.ae_integrable_e] with z h1 h2 h3 hi
  rw [Φσ, h1, Pi.add_apply, accL, h2, h3]
  have hsplit : ∀ ζ, (if σ.1 (M.ω z ζ, z) then M.e z ζ else h z) =
      (if σ.1 (M.ω z ζ, z) then M.e z ζ else 0) + h z * (if σ.1 (M.ω z ζ, z) then 0 else 1) :=
    fun ζ => by split_ifs <;> ring
  have hm1 : Measurable fun ζ => σ.1 (M.ω z ζ, z) :=
    (M.measurable_pair σ).comp measurable_prodMk_left
  have hi1 : Integrable (fun ζ => if σ.1 (M.ω z ζ, z) then M.e z ζ else 0) M.ν :=
    hi.norm.mono' (Measurable.ite (hm1 (measurableSet_singleton true))
      (M.measurable_e.comp measurable_prodMk_left) measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun ζ => by
        split_ifs
        · exact le_rfl
        · simp)
  have hi2 : Integrable (fun ζ => h z * (if σ.1 (M.ω z ζ, z) then (0 : ℝ) else 1)) M.ν :=
    (Integrable.of_bound (Measurable.ite (hm1 (measurableSet_singleton true)) measurable_const
      measurable_const).aestronglyMeasurable 1 (Eventually.of_forall fun ζ => by
        split_ifs <;> norm_num)).const_mul _
  simp_rw [hsplit]
  rw [integral_add hi1 hi2, integral_const_mul, mul_comm]
  rfl

/-- `Φh = ∫ max{e, h(z')} ν(dζ')`. -/
noncomputable def ΦmaxF (h : Lp ℝ 1 M.φ) (z : Z) : ℝ := ∫ ζ, max (M.e z ζ) (h z) ∂M.ν

theorem measurable_ΦmaxF (h : Lp ℝ 1 M.φ) : Measurable (M.ΦmaxF h) := by
  have hm : Measurable fun p : Z × Ξ => max (M.e p.1 p.2) (h p.1) :=
    M.measurable_e.max ((Lp.stronglyMeasurable h).measurable.comp measurable_fst)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := M.ν)).measurable

theorem integrable_ΦmaxF (h : Lp ℝ 1 M.φ) : Integrable (M.ΦmaxF h) M.φ := by
  refine (M.integrable_absInt.add (L1.integrable_coeFn h).abs).mono'
    (M.measurable_ΦmaxF h).aestronglyMeasurable ?_
  filter_upwards [M.ae_integrable_e] with z hi
  rw [Real.norm_eq_abs, Pi.add_apply]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ζ, |max (M.e z ζ) (h z)| ∂M.ν ≤ ∫ ζ, (|M.e z ζ| + |h z|) ∂M.ν :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hi.abs.add (integrable_const _)) (Eventually.of_forall fun ζ => by
            rw [abs_le]
            constructor
            · linarith [le_max_left (M.e z ζ) (h z), neg_abs_le (M.e z ζ), abs_nonneg (h z)]
            · exact max_le (by linarith [le_abs_self (M.e z ζ), abs_nonneg (h z)])
                (by linarith [le_abs_self (h z), abs_nonneg (M.e z ζ)]))
    _ = ∫ ζ, |M.e z ζ| ∂M.ν + |h z| := by
        rw [integral_add hi.abs (integrable_const _)]
        simp

/-- `Φh` in `L¹(φ)`. -/
noncomputable def Φmax (h : Lp ℝ 1 M.φ) : Lp ℝ 1 M.φ := (M.integrable_ΦmaxF h).toL1 _

/-- The policy of Exercise 8.1.21: accept when `w'/(1 − β) ≥ h(z')`. -/
noncomputable def accept (h : Lp ℝ 1 M.φ) : StopPolicy (ℝ × Z) :=
  acceptWhere (s := fun p : ℝ × Z => p.1 / (1 - M.β)) (h := fun p => h p.2)
    (measurable_fst.div_const _) ((Lp.stronglyMeasurable h).measurable.comp measurable_snd)

theorem integrable_choice (σ : StopPolicy (ℝ × Z)) (h : Lp ℝ 1 M.φ) {z : Z}
    (hi : Integrable (M.e z) M.ν) :
    Integrable (fun ζ => if σ.1 (M.ω z ζ, z) then M.e z ζ else h z) M.ν := by
  have hm1 : Measurable fun ζ => σ.1 (M.ω z ζ, z) :=
    (M.measurable_pair σ).comp measurable_prodMk_left
  refine (hi.abs.add (integrable_const |h z|)).mono' (Measurable.ite
    (hm1 (measurableSet_singleton true)) (M.measurable_e.comp measurable_prodMk_left)
    measurable_const).aestronglyMeasurable (Eventually.of_forall fun ζ => ?_)
  rw [Real.norm_eq_abs, Pi.add_apply]
  split_ifs
  · exact le_add_of_nonneg_right (abs_nonneg _)
  · exact le_add_of_nonneg_left (abs_nonneg _)

theorem integrable_max_e (h : Lp ℝ 1 M.φ) {z : Z} (hi : Integrable (M.e z) M.ν) :
    Integrable (fun ζ => max (M.e z ζ) (h z)) M.ν :=
  hi.sup (integrable_const (h z))

theorem Φσ_le_Φmax (σ : StopPolicy (ℝ × Z)) (h : Lp ℝ 1 M.φ) : M.Φσ σ h ≤ M.Φmax h := by
  rw [← Lp.coeFn_le]
  filter_upwards [M.Φσ_coeFn σ h, (M.integrable_ΦmaxF h).coeFn_toL1, M.ae_integrable_e]
    with z h1 h2 hi
  rw [Φmax, h1, h2, ΦmaxF]
  refine integral_mono (M.integrable_choice σ h hi) (M.integrable_max_e h hi) fun ζ => ?_
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem Φσ_accept (h : Lp ℝ 1 M.φ) : M.Φσ (M.accept h) h = M.Φmax h := by
  refine Lp.ext ?_
  filter_upwards [M.Φσ_coeFn (M.accept h) h, (M.integrable_ΦmaxF h).coeFn_toL1] with z h1 h2
  rw [Φmax, h1, h2, ΦmaxF]
  refine integral_congr_ae (Eventually.of_forall fun ζ => ?_)
  exact acceptWhere_apply (s := fun p : ℝ × Z => p.1 / (1 - M.β)) (h := fun p => h p.2)
    (measurable_fst.div_const _) ((Lp.stronglyMeasurable h).measurable.comp measurable_snd)
    (M.ω z ζ, z)

/-- The continuation value Bellman operator (8.29), `T̂h = c + βP(Φh)`. -/
noncomputable def That (h : Lp ℝ 1 M.φ) : Lp ℝ 1 M.φ := M.cconst + M.β • M.Pop (M.Φmax h)

/-- **Exercises 8.1.21–8.1.22** (p. 260): the policy `σ(w', z') = 𝟙{w'/(1 − β) ≥ h(z')}` is
`h`-greedy, and the Bellman operator is (8.29), `(T̂h)(z) = c + β 𝔼_z max{w'/(1 − β), h(z')}`, i.e.
`T̂h = c + βP(Φh)`, `(Φh)(z') = ∫ max{ω(z', ζ')/(1 − β), h(z')} ν(dζ')`. -/
theorem exercise_8_1_21_22 (h : Lp ℝ 1 M.φ) :
    M.adp.IsGreedy h (M.accept h) ∧ M.adp.bellman h = M.That h := by
  have hT : M.adp.T (M.accept h) h = M.That h := by rw [T_eq, Φσ_accept]; rfl
  have hg : M.adp.IsGreedy h (M.accept h) := fun τ => by
    rw [T_eq, T_eq]
    exact add_le_add le_rfl (M.smul_le_smul'
      ((L1.markovCLM_isPositive M.stationary).mono ((M.Φσ_le_Φmax τ h).trans
        (by rw [Φσ_accept]))))
  refine ⟨hg, ?_⟩
  rw [← hT]
  exact le_antisymm (M.adp.isGreedy_greedy ⟨_, hg⟩ _) (hg _) |>.symm

theorem regular : M.adp.Regular := fun h => ⟨_, (M.exercise_8_1_21_22 h).1⟩

/-- The Bellman operator (8.29) almost everywhere:
`(T̂h)(z) = c + β ∫ ∫ max{ω(z', ζ')/(1 − β), h(z')} ν(dζ') P(z, dz')`. -/
theorem That_coeFn (h : Lp ℝ 1 M.φ) :
    ⇑(M.That h) =ᵐ[M.φ] fun z => M.c + M.β * ∫ z', M.ΦmaxF h z' ∂(M.P z) := by
  filter_upwards [Lp.coeFn_add M.cconst (M.β • M.Pop (M.Φmax h)),
    (memLp_const (μ := M.φ) M.c).coeFn_toLp, Lp.coeFn_smul M.β (M.Pop (M.Φmax h)),
    L1.markovCLM_coeFn M.stationary (M.Φmax h),
    L1.markovFun_congr M.stationary (M.integrable_ΦmaxF h).coeFn_toL1] with z h1 h2 h3 h4 h5
  rw [That, h1, Pi.add_apply]
  change M.cconst z + (M.β • M.Pop (M.Φmax h)) z = _
  rw [h3, Pi.smul_apply, smul_eq_mul]
  change ((memLp_const M.c).toLp _) z + M.β * (L1.markovCLM M.stationary (M.Φmax h)) z = _
  rw [h2, h4]
  change M.c + M.β * L1.markovFun (M.Φmax h) z = _
  rw [show L1.markovFun (M.Φmax h) z = _ from h5]

/-- **Exercise 8.1.23** (p. 260): `T̂` is a contraction of modulus `β` on `L¹(φ)`. -/
theorem exercise_8_1_23 (g h : Lp ℝ 1 M.φ) : ‖M.That g - M.That h‖ ≤ M.β * ‖g - h‖ := by
  rw [That, That, add_sub_add_left_eq_sub, ← smul_sub, ← map_sub, norm_smul,
    Real.norm_of_nonneg M.β_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ M.β_nonneg
  refine (M.Pop.le_opNorm _).trans ?_
  refine (mul_le_mul_of_nonneg_right (L1.markovCLM_norm_le M.stationary) (norm_nonneg _)).trans ?_
  rw [one_mul, L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  refine integral_mono_ae (L1.integrable_coeFn _).norm (L1.integrable_coeFn _).norm ?_
  filter_upwards [Lp.coeFn_sub (M.Φmax g) (M.Φmax h), Lp.coeFn_sub g h,
    (M.integrable_ΦmaxF g).coeFn_toL1, (M.integrable_ΦmaxF h).coeFn_toL1, M.ae_integrable_e]
    with z h1 h2 h3 h4 hi
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs]
  change |(M.Φmax g) z - (M.Φmax h) z| ≤ _
  rw [Φmax, Φmax, h3, h4, ΦmaxF, ΦmaxF, ← integral_sub (M.integrable_max_e g hi)
    (M.integrable_max_e h hi)]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ ζ, |max (M.e z ζ) (g z) - max (M.e z ζ) (h z)| ∂M.ν ≤ ∫ _, |g z - h z| ∂M.ν :=
        integral_mono ((M.integrable_max_e g hi).sub (M.integrable_max_e h hi)).abs
          (integrable_const _) fun ζ => by
            rw [max_comm _ (g z), max_comm _ (h z)]
            exact abs_max_sub_max_le_abs _ _ _
    _ = |g z - h z| := by simp

theorem That_contracting : ContractingWith ⟨M.β, M.β_nonneg⟩ M.That :=
  ⟨M.β_lt_one, LipschitzWith.of_dist_le_mul fun g h => by
    rw [dist_eq_norm, dist_eq_norm]
    exact M.exercise_8_1_23 g h⟩

theorem That_mono : Monotone M.That := fun g h hgh => by
  refine add_le_add le_rfl (M.smul_le_smul'
    ((L1.markovCLM_isPositive M.stationary).mono ?_))
  rw [← Lp.coeFn_le]
  filter_upwards [(M.integrable_ΦmaxF g).coeFn_toL1, (M.integrable_ΦmaxF h).coeFn_toL1,
    (Lp.coeFn_le _ _).2 hgh, M.ae_integrable_e] with z h1 h2 h3 hi
  rw [Φmax, Φmax, h1, h2]
  exact integral_mono (M.integrable_max_e g hi) (M.integrable_max_e h hi) fun ζ =>
    max_le_max le_rfl h3

theorem isAdditive : BanachLattice.IsAdditive id M.adp M.mσ M.Kσ :=
  ⟨M.Kσ_isPositive, fun _ _ => rfl⟩

/-- §8.1.3.3 (p. 260): by Theorem 4.1.8, the fundamental optimality properties hold for
`(L¹(φ), 𝕋̂)` and VFI, OPI and HPI converge. -/
theorem section_8_1_3_3 :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧ ∃ vstar,
      M.adp.VFIGeometric univ vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar := by
  have hD := BanachLattice.example_4_1_1 M.D_isPositive M.specRad_D_lt_one
  have hsr : M.adp.IsSemiRegular univ := ⟨isClosed_univ, fun v _ => M.regular v, mapsTo_univ _ _⟩
  obtain ⟨hw, hFO, vstar, -, hgeo, hconv⟩ := BanachLattice.theorem_4_1_8
    (isIsoOrderEmbedding_id_L1 M.φ) M.adp M.isAdditive hD M.Kσ_le_D hsr univ_nonempty
  exact ⟨hw, hFO, vstar, hgeo, hconv M.regular⟩

/-- The model with unemployment compensation `c'`. -/
abbrev withC (c' : ℝ) : PersistentSearch Z Ξ := { M with c := c' }

/-- **Exercise 8.1.24** (p. 260): if `c_a ≤ c_b`, the fixed points of the corresponding
continuation value operators satisfy `h_a ≤ h_b` (almost everywhere, the order of `L¹(φ)`). -/
theorem exercise_8_1_24 {ca cb : ℝ} (hc : ca ≤ cb) :
    ContractingWith.fixedPoint _ (M.withC ca).That_contracting ≤
      ContractingWith.fixedPoint _ (M.withC cb).That_contracting := by
  refine fixedPoint_ge_of_le (M.withC cb).That_contracting (M.withC cb).That_mono (fun h => ?_)
    (ContractingWith.fixedPoint_isFixedPt (M.withC ca).That_contracting)
  refine add_le_add ?_ le_rfl
  rw [← Lp.coeFn_le]
  filter_upwards [(memLp_const (μ := M.φ) ca).coeFn_toLp, (memLp_const (μ := M.φ) cb).coeFn_toLp]
    with z h1 h2
  change ((memLp_const ca).toLp _) z ≤ ((memLp_const cb).toLp _) z
  rw [h1, h2]
  exact hc

end PersistentSearch

end SargentStachurski.AdditionalApplications
