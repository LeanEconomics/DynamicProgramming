/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InfiniteHorizonDP.EUMaxPrinciple
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# §7.4: the remark after Theorem 7.4.1 (linear `φ` and the sign of `μ*`)

Miao, p. 220: "if `φ` is linear in `(x, a)`, then the assumption of `μ*_{t+1} ≥ 0` is not
needed." The assumption `μ* ≥ 0` is used twice in the proof of Theorem 7.4.1: for the concavity
of the Hamiltonian, and in the last step `−E β^{T+1} μ*_{T+1}(x*_{T+1} − x_{T+1}) ≥
−E β^{T+1} μ*_{T+1} x*_{T+1}`, which needs `μ*_{T+1} x_{T+1} ≥ 0`. Linearity (or affinity) of
`φ` removes only the first use.

* `remark_7_4_1_affine` (**corrected remark**): if `φ(·, ·, z, z′)` is affine on `X × A` (linear
  is a special case), `μ* ≥ 0` can be dropped from the concavity step; the conclusion of
  Theorem 7.4.1 holds against every feasible plan with `E[μ*_{T+1} x_{T+1}] ≥ 0` for all `T`.
* `remark_7_4_1_counterexample` (**the printed remark is false**): a deterministic model with
  `X = A = Γ(x) = ℝ₊`, `x_{t+1} = φ(x_t, a_t) = a_t` (linear), `β = 1/2` and
  `u(x, a) = −x + 3a/8 − 1/(1 + x)`, which satisfies Assumptions 6.4.12, 6.4.14, 7.3.3 (with the
  strict inequality) and 7.3.4. The constant plan `x*_t = a*_t = 1` with `μ*_t = −3/4` is interior
  and satisfies (7.30), (7.31) and (7.32), but the plan `x_t = 8ᵗ` has partial sums larger by at
  least `1` at every horizon, so the conclusion of Theorem 7.4.1 fails.
-/

namespace Miao.InfiniteHorizonDP

open MeasureTheory ProbabilityTheory Filter Topology

namespace OCModel

variable {Z : Type*} [MeasurableSpace Z] {Ω : Type*} {m0 : MeasurableSpace Ω}
  {M : OCModel ℝ ℝ Z} {P : Measure Ω} {ℱ : Filtration ℕ m0} {z : ℕ → Ω → Z}

/-- **The remark after Theorem 7.4.1, corrected** (Miao, p. 220). If `φ(·, ·, z, z′)` is affine on
`X × A`, the sign condition `μ*_{t+1} ≥ 0` is not needed for the concavity of the Hamiltonian;
the last step of the proof needs instead `E[μ*_{T+1} x_{T+1}] ≥ 0` for the competing plan. Under
the other hypotheses of Theorem 7.4.1, every feasible plan `a` with this property satisfies
`S_T(a) ≤ S_T(as) + w_T` with `w_T → 0`. -/
theorem remark_7_4_1_affine [IsProbabilityMeasure P] (hz : ∀ t, Measurable[ℱ t] (z t))
    (hφm : Measurable fun p : ℝ × ℝ × Z × Z => M.φ p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hXc : Convex ℝ M.X) (hAc : Convex ℝ M.A)
    (hΓA : ∀ x z', M.Γ x z' ⊆ M.A) (h512 : 0 < M.β ∧ M.β < 1)
    (haff : ∀ z' z'', ∀ p ∈ M.X ×ˢ M.A, ∀ q ∈ M.X ×ˢ M.A, ∀ θ η : ℝ, 0 ≤ θ → 0 ≤ η →
      θ + η = 1 → M.φ (θ • p + η • q).1 (θ • p + η • q).2 z' z'' =
        θ * M.φ p.1 p.2 z' z'' + η * M.φ q.1 q.2 z' z'')
    (h6414 : M.Assumption6414) (h733 : M.eu_Assumption733) (h734 : M.eu_Assumption734) (x₀ : ℝ)
    {μ as a : ℕ → Ω → ℝ} (has : M.eu_IsPlanInf ℱ z x₀ as) (ha : M.eu_IsPlanInf ℱ z x₀ a)
    (hmp : eu_MPInf P ℱ z M μ (M.path z as x₀) as)
    (htvc : Tendsto (fun T => M.β ^ T * ∫ ω, μ T ω * M.path z as x₀ T ω ∂P) atTop (𝓝 0))
    (hμxi : ∀ T, Integrable (fun ω => μ T ω * M.path z as x₀ T ω) P)
    (hint_a : ∀ t ω, as t ω ∈ interior (M.Γ (M.path z as x₀ t ω) (z t ω)))
    (hint_x : ∀ t ω, M.path z as x₀ t ω ∈ interior M.X)
    (hint : eu_MPIntInf P z M μ (M.path z as x₀) as (M.path z a x₀) a)
    (hbd : ∀ T, 0 ≤ ∫ ω, μ (T + 1) ω * M.path z a x₀ (T + 1) ω ∂P) :
    ∃ w : ℕ → ℝ, Tendsto w atTop (𝓝 0) ∧
      ∀ T, M.eu_partialJ P z a x₀ T ≤ M.eu_partialJ P z as x₀ T + w T := by
  have hβ : 0 ≤ M.β := h512.1.le
  have hmemA : ∀ t ω, (M.path z as x₀ t ω, as t ω) ∈ interior (M.X ×ˢ M.A) := fun t ω => by
    rw [interior_prod_eq]
    exact ⟨hint_x t ω, interior_mono (hΓA _ _) (hint_a t ω)⟩
  have hsX : ∀ t ω, (M.path z as x₀ t ω, as t ω) ∈ M.X ×ˢ M.A := fun t ω =>
    interior_subset (hmemA t ω)
  have hcX : ∀ t ω, (M.path z a x₀ t ω, a t ω) ∈ M.X ×ˢ M.A := fun t ω =>
    ⟨(ha.2 t ω).1, hΓA _ _ (ha.2 t ω).2⟩
  have hud : ∀ t ω, DifferentiableAt ℝ (fun p : ℝ × ℝ => M.u t p.1 (z t ω) p.2)
      (M.path z as x₀ t ω, as t ω) := fun t ω =>
    ((h734 t (z t ω)).differentiableOn one_ne_zero).differentiableAt
      (isOpen_interior.mem_nhds (hmemA t ω))
  have hφd : ∀ t ω, DifferentiableAt ℝ (fun p : ℝ × ℝ => M.φ p.1 p.2 (z t ω) (z (t + 1) ω))
      (M.path z as x₀ t ω, as t ω) := fun t ω =>
    (h6414 (z t ω) (z (t + 1) ω)).differentiableAt (isOpen_interior.mem_nhds (hmemA t ω))
  have hH : ∀ t ω, ConcaveOn ℝ (M.X ×ˢ M.A) (M.pathHam z μ t ω) := fun t ω => by
    have hl : ConcaveOn ℝ (M.X ×ˢ M.A) fun p : ℝ × ℝ =>
        M.β * (μ (t + 1) ω * M.φ p.1 p.2 (z t ω) (z (t + 1) ω)) := by
      refine ⟨hXc.prod hAc, fun p hp q hq θ η hθ hη hs => ?_⟩
      simp only [smul_eq_mul]
      rw [haff (z t ω) (z (t + 1) ω) p hp q hq θ η hθ hη hs]
      nlinarith
    exact (eu_concaveOn_of_733 h733 hXc hAc t (z t ω)).add hl
  refine ⟨fun T => M.β ^ (T + 1) * ∫ ω, μ (T + 1) ω * M.path z as x₀ (T + 1) ω ∂P,
    htvc.comp (tendsto_add_atTop_nat 1), fun T => ?_⟩
  have hcore := eu_mp_core hz hφm hβ x₀ has.1 ha.1 hsX hcX hmp hH hud hφd hint T
  have hμx : Integrable (fun ω => μ (T + 1) ω * M.path z a x₀ (T + 1) ω) P := by
    have := (hμxi (T + 1)).sub (hint.μΔ T)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply]
    ring
  have hsplit : ∫ ω, μ (T + 1) ω * (M.path z as x₀ (T + 1) ω - M.path z a x₀ (T + 1) ω) ∂P =
      (∫ ω, μ (T + 1) ω * M.path z as x₀ (T + 1) ω ∂P) -
        ∫ ω, μ (T + 1) ω * M.path z a x₀ (T + 1) ω ∂P := by
    rw [← integral_sub (hμxi (T + 1)) hμx]
    congr 1
    funext ω
    ring
  rw [hsplit] at hcore
  have := mul_le_mul_of_nonneg_left (hbd T) (pow_nonneg hβ (T + 1))
  nlinarith

end OCModel

/-! ### The counterexample -/

/-- The model of the counterexample to the remark after Theorem 7.4.1: `X = A = Γ(x) = ℝ₊`,
`φ(x, a) = a`, `u(x, a) = −x + 3a/8 − 1/(1 + x)`, `β = 1/2`, no shocks. -/
noncomputable def eu_remModel : OCModel ℝ ℝ Unit where
  X := Set.Ici 0
  A := Set.Ici 0
  Q := 0
  Γ := fun _ _ => Set.Ici 0
  φ := fun _ a _ _ => a
  u := fun _ x _ a => -x + 3 / 8 * a - 1 / (1 + x)
  uT := fun _ _ => 0
  β := 1 / 2
  T := 0

/-- `d/dx [−x + 3a/8 − 1/(1 + x)] = −1 + 1/(1 + x)²` for `x > −1`. -/
theorem eu_rem_hasDerivAt_x {x : ℝ} (hx : -1 < x) (a : ℝ) :
    HasDerivAt (fun y : ℝ => -y + 3 / 8 * a - 1 / (1 + y)) (-1 + 1 / (1 + x) ^ 2) x := by
  have h1 : (1 + x) ≠ 0 := by linarith
  have hc : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_id x).const_add 1
  have hinv := HasDerivAt.inv hc h1
  have h := ((hasDerivAt_id x).neg.add_const (3 / 8 * a)).sub hinv
  have e : (fun y : ℝ => -y + 3 / 8 * a - 1 / (1 + y)) =
      fun y => -id y + 3 / 8 * a - (1 + y)⁻¹ := by
    funext y; simp [one_div]
  rw [e]
  exact h.congr_deriv (by ring)

/-- **The remark after Theorem 7.4.1 is false as printed** (Miao, p. 220). In the model
`eu_remModel` (`φ(x, a) = a` linear, Assumptions 6.4.12, 6.4.14, 7.3.3 with the strict inequality,
and 7.3.4), on any filtered probability space, the constant plan `a*_t = 1` (states `x*_t = 1`)
with multipliers `μ*_t = −3/4 < 0` is interior and satisfies (7.30), (7.31) and the transversality
condition (7.32); yet the plan `a_t = 8^{t+1}` (states `x_t = 8ᵗ`), feasible and integrable, has
`S_T(a) ≥ S_T(a*) + 1` for every `T`, so the conclusion of Theorem 7.4.1 fails. -/
theorem remark_7_4_1_counterexample {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) :
    let M := eu_remModel
    let z : ℕ → Ω → Unit := fun _ _ => ()
    let as : ℕ → Ω → ℝ := fun _ _ => 1
    let μ : ℕ → Ω → ℝ := fun _ _ => -3 / 4
    let a : ℕ → Ω → ℝ := fun t _ => 8 ^ (t + 1)
    (∀ p q : ℝ × ℝ, ∀ θ η : ℝ, M.φ (θ • p + η • q).1 (θ • p + η • q).2 () () =
      θ * M.φ p.1 p.2 () () + η * M.φ q.1 q.2 () ()) ∧
    M.Assumption6412 ∧ M.Assumption6414 ∧ M.eu_Assumption733 ∧ M.eu_Assumption734 ∧
    (∀ t ω, μ (t + 1) ω < 0) ∧
    OCModel.eu_MPInf P ℱ z M μ (M.path z as 1) as ∧
    Tendsto (fun T => M.β ^ T * ∫ ω, μ T ω * M.path z as 1 T ω ∂P) atTop (𝓝 0) ∧
    (∀ t ω, as t ω ∈ interior (M.Γ (M.path z as 1 t ω) (z t ω))) ∧
    (∀ t ω, M.path z as 1 t ω ∈ interior M.X) ∧
    M.eu_IsPlanInf ℱ z 1 as ∧ M.eu_IsPlanInf ℱ z 1 a ∧
    OCModel.eu_MPIntInf P z M μ (M.path z as 1) as (M.path z a 1) a ∧
    (∀ T, M.eu_partialJ P z as 1 T + 1 ≤ M.eu_partialJ P z a 1 T) ∧
    ¬ ∃ w : ℕ → ℝ, Tendsto w atTop (𝓝 0) ∧
      ∀ T, M.eu_partialJ P z a 1 T ≤ M.eu_partialJ P z as 1 T + w T := by
  intro M z as μ a
  have hps : ∀ t ω, M.path z as 1 t ω = 1 := fun t ω => by
    cases t with
    | zero => rfl
    | succ t => rfl
  have hpc : ∀ t ω, M.path z a 1 t ω = 8 ^ t := fun t ω => by
    cases t with
    | zero => simp [OCModel.path]
    | succ t => rfl
  have hint_iX : interior M.X = Set.Ioi 0 := interior_Ici
  -- the derivatives along the candidate
  have hda : ∀ t (w : Unit) (x : ℝ), deriv (fun b => M.u t x w b) 1 = 3 / 8 := fun t w x => by
    have : HasDerivAt (fun b : ℝ => -x + 3 / 8 * b - 1 / (1 + x)) (3 / 8) 1 := by
      have := (((hasDerivAt_id (1 : ℝ)).const_mul (3 / 8 : ℝ)).const_add (-x)).sub_const
        (1 / (1 + x))
      simpa using this
    exact this.deriv
  have hdx : ∀ t (w : Unit), deriv (fun y => M.u t y w 1) 1 = -3 / 4 := fun t w => by
    have := (eu_rem_hasDerivAt_x (by norm_num : (-1 : ℝ) < 1) 1).deriv
    change deriv (fun y : ℝ => -y + 3 / 8 * 1 - 1 / (1 + y)) 1 = _
    rw [this]; norm_num
  have hφa : ∀ (x : ℝ) (w w' : Unit), deriv (fun b => M.φ x b w w') 1 = 1 :=
    fun x w w' => deriv_id 1
  have hφx : ∀ (b : ℝ) (w w' : Unit), deriv (fun y => M.φ y b w w') 1 = 0 :=
    fun b w w' => deriv_const 1 b
  have hgap : ∀ T, M.eu_partialJ P z as 1 T + 1 ≤ M.eu_partialJ P z a 1 T := by
    intro T
    have key : ∀ t ∈ Finset.range (T + 1), M.β ^ t * ∫ ω, M.u t (M.path z as 1 t ω) (z t ω)
        (as t ω) ∂P + (if t = 0 then 1 else 0) ≤
        M.β ^ t * ∫ ω, M.u t (M.path z a 1 t ω) (z t ω) (a t ω) ∂P := by
      intro t _
      simp only [hps, hpc]
      simp only [M, eu_remModel, as, a, integral_const, probReal_univ, smul_eq_mul, one_mul]
      have hp : 0 < (1 / 2 : ℝ) ^ t := by positivity
      have hq : (1 : ℝ) ≤ 8 ^ t := one_le_pow₀ (by norm_num)
      have hr : 1 / (1 + (8 : ℝ) ^ t) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
      have e : (3 : ℝ) / 8 * 8 ^ (t + 1) = 3 * 8 ^ t := by rw [pow_succ]; ring
      rw [e]
      split_ifs with ht
      · subst ht; norm_num
      · nlinarith
    have hs := Finset.sum_le_sum key
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (T + 1)) 0] at hs
    simp only [Finset.mem_range, Nat.zero_lt_succ, ↓reduceIte] at hs
    simpa [OCModel.eu_partialJ] using hs
  refine ⟨fun p q θ η => rfl, ?_, ?_, ?_, ?_, fun t ω => by norm_num [μ], ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro _ _ x _ x' _ b _ b' _ θ η _ _ _
    simp [M, eu_remModel]
  · intro _ _
    exact (differentiable_snd).differentiableOn
  · intro t _ x hx x' hx' b _ b' _ θ η hθ hη hs
    simp only [M, eu_remModel, Set.mem_Ici] at hx hx' ⊢
    have hx1 : 0 < 1 + x := by linarith
    have hx1' : 0 < 1 + x' := by linarith
    have hm : 0 < 1 + (θ * x + η * x') := by nlinarith
    have key : 1 / (1 + (θ * x + η * x')) * ((1 + x) * (1 + x')) * (1 + (θ * x + η * x')) =
        (1 + x) * (1 + x') := by field_simp
    have hcvx : 1 / (1 + (θ * x + η * x')) ≤ θ * (1 / (1 + x)) + η * (1 / (1 + x')) := by
      rw [div_le_iff₀ hm]
      have e : (θ * (1 / (1 + x)) + η * (1 / (1 + x'))) * (1 + (θ * x + η * x')) =
          (θ * (1 + x') + η * (1 + x)) * (1 + (θ * x + η * x')) / ((1 + x) * (1 + x')) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      have hη' : η = 1 - θ := by linarith
      subst hη'
      nlinarith [sq_nonneg (x - x'), mul_nonneg hθ.le hη.le]
    refine ⟨by nlinarith, fun hne => ?_⟩
    have hcvx' : 1 / (1 + (θ * x + η * x')) < θ * (1 / (1 + x)) + η * (1 / (1 + x')) := by
      rw [div_lt_iff₀ hm]
      have e : (θ * (1 / (1 + x)) + η * (1 / (1 + x'))) * (1 + (θ * x + η * x')) =
          (θ * (1 + x') + η * (1 + x)) * (1 + (θ * x + η * x')) / ((1 + x) * (1 + x')) := by
        field_simp
      rw [e, lt_div_iff₀ (by positivity)]
      have hη' : η = 1 - θ := by linarith
      subst hη'
      have hsq : 0 < (x - x') ^ 2 := by
        have : x - x' ≠ 0 := sub_ne_zero.2 hne
        positivity
      nlinarith [mul_pos hθ hη, mul_pos (mul_pos hθ hη) hsq]
    nlinarith
  · intro t _
    have hint : interior (M.X ×ˢ M.A) = Set.Ioi 0 ×ˢ Set.Ioi 0 := by
      rw [interior_prod_eq]; simp [M, eu_remModel]
    rw [hint]
    have : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => -p.1 + 3 / 8 * p.2 - (1 + p.1)⁻¹)
        (Set.Ioi 0 ×ˢ Set.Ioi 0) := by
      refine ContDiffOn.sub (by fun_prop) (ContDiffOn.inv (by fun_prop) fun p hp => ?_)
      have : (0 : ℝ) < p.1 := hp.1
      linarith
    refine this.congr fun p _ => ?_
    simp [M, eu_remModel, one_div]
  · refine ⟨fun t => ?_, fun t _ => ?_⟩
    · refine Eventually.of_forall fun ω => ?_
      simp only [OCModel.Ha, Pi.zero_apply, hps, as]
      simp only [hda, hφa, μ, mul_one]
      rw [condExp_const (ℱ.le t)]
      norm_num [M, eu_remModel]
    · refine Eventually.of_forall fun ω => ?_
      simp only [OCModel.Hx, hps, as]
      simp only [hdx, hφx, μ, mul_zero]
      rw [condExp_const (ℱ.le t)]
      norm_num
  · have : (fun T => M.β ^ T * ∫ ω, μ T ω * M.path z as 1 T ω ∂P) =
        fun T => -3 / 4 * (1 / 2 : ℝ) ^ T := by
      funext T
      simp only [hps, μ]
      simp [M, eu_remModel, mul_comm]
    rw [this]
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (-3 / 4 : ℝ)
    simpa using this
  · intro t ω
    rw [hps]
    simp [M, eu_remModel, as]
  · intro t ω
    rw [hps, hint_iX]
    simp
  · refine ⟨fun t => measurable_const, fun t ω => ?_⟩
    rw [hps]
    simp [M, eu_remModel, as]
  · refine ⟨fun t => measurable_const, fun t ω => ?_⟩
    rw [hpc]
    simp only [M, eu_remModel, Set.mem_Ici, a]
    exact ⟨by positivity, by positivity⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro t <;>
      simp only [hps, hpc, as, a, μ, z] <;> exact integrable_const _
  · exact hgap
  · rintro ⟨w, hw, hle⟩
    obtain ⟨T, hT⟩ := ((tendsto_order.1 hw).2 1 one_pos).exists
    have := hgap T
    have := hle T
    linarith

end Miao.InfiniteHorizonDP
