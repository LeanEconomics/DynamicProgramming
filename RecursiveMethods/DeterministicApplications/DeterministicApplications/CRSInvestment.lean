/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DeterministicApplications.ConstantReturnsDP
import DeterministicApplications.WeightedBellman

/-!
# Investment with constant returns

SLP §5.10, pp. 113–114: output `F(k, y)` depends on current and end-of-period capital, `F` has
constant returns, and `(1 − δ)k ≤ y ≤ (1 + α)k`. The firm solves
`v(k) = max_{y ∈ Γ(k)} {pF(k, y) − q[y − (1 − δ)k] + βv(y)}` on `k ≥ 0`.

With `β(1 + α) < 1`, Assumptions 4.10–4.11 hold (`crs_assumption410`, `crs_assumption411`); this
is what must be assumed about `α` and `β`.

* **Exercise 5.10a** (`ex_5_10a`): `v*` is homogeneous of degree one.
* **Exercise 5.10b**: `solvesFE_rescale`: if `v` solves the functional equation, so does
  `k ↦ v(ak)/a` for every `a > 0`. `ex_5_10b`: every solution with `|v(k)| ≤ Ck` is `v*`, hence
  homogeneous of degree one. (Some growth bound is needed: Theorem 4.3 is what rules out other
  solutions.)
* **Exercise 5.10c** (`ex_5_10c`): the solution is `v(k) = Ak` with
  `A = max_{θ ∈ [1 − δ, 1 + α]} [pF(1, θ) − q(θ − (1 − δ)) + βAθ]`; the policy is `g(k) = θk` with
  `θ` the maximizer, unique when `F(1, ·)` is strictly concave (which homogeneity and strict
  quasi-concavity give, Exercise 4.8b); `v = v*`; and the plan `k_t = θᵗk₀` is optimal.
-/

open Set Filter Topology

namespace StokeyLucasPrescott.DeterministicApplications

/-- The state space `[0, ∞)` of capital. -/
abbrev CapStock := ↥(Ici (0 : ℝ))

theorem isCone_Ici : IsCone (Ici (0 : ℝ)) := fun x hx a ha => by
  simp only [smul_eq_mul, Set.mem_Ici] at hx ⊢; exact mul_nonneg ha hx

variable {Fk : ℝ → ℝ → ℝ} {p q δ α β : ℝ}

/-- `Γ(k) = [(1 − δ)k, (1 + α)k]`. -/
def crsΓ (δ α : ℝ) (k : CapStock) : Set CapStock := {y | (1 - δ) * k.1 ≤ y.1 ∧ y.1 ≤ (1 + α) * k.1}

/-- The return `pF(k, y) − q[y − (1 − δ)k]`. -/
def crsH (Fk : ℝ → ℝ → ℝ) (p q δ : ℝ) (pr : CapStock × CapStock) : ℝ :=
  p * Fk pr.1.1 pr.2.1 - q * (pr.2.1 - (1 - δ) * pr.1.1)

/-- The hypotheses of SLP §5.10 used here. -/
structure CRSInvHyp (Fk : ℝ → ℝ → ℝ) (p q δ α β : ℝ) : Prop where
  δ_pos : 0 < δ
  δ_lt : δ < 1
  α_pos : 0 < α
  β_pos : 0 < β
  discount : β * (1 + α) < 1
  p_nonneg : 0 ≤ p
  q_nonneg : 0 ≤ q
  F_cont : ContinuousOn (fun z : ℝ × ℝ => Fk z.1 z.2) (Set.Ici 0 ×ˢ Set.Ici 0)
  F_hom : ∀ a k y, 0 ≤ a → 0 ≤ k → 0 ≤ y → Fk (a * k) (a * y) = a * Fk k y

theorem CRSInvHyp.β_lt (h : CRSInvHyp Fk p q δ α β) : β < 1 := by
  nlinarith [h.discount, h.β_pos, h.α_pos]

/-- Assumption 4.10 holds with growth factor `1 + α`. -/
theorem crs_assumption410 (h : CRSInvHyp Fk p q δ α β) :
    Assumption410 isCone_Ici (crsΓ δ α) β (1 + α) := by
  have hemb := (isClosed_Ici (a := (0 : ℝ))).isClosedEmbedding_subtypeVal
  have hδ := h.δ_lt
  have hδ0 := h.δ_pos
  have hα := h.α_pos
  have hself : ∀ k : CapStock, k ∈ crsΓ δ α k := fun k =>
    ⟨by nlinarith [k.2.out, h.δ_pos], by nlinarith [k.2.out]⟩
  refine ⟨convex_Ici 0, fun k => ⟨k, hself k⟩, fun k => hemb.isCompact_preimage isCompact_Icc,
    fun k => ⟨⟨k, hself k⟩, fun y hy ks hks => ?_⟩,
    fun k => ⟨⟨k, hself k⟩, fun ks hks ys hys => ?_⟩,
    fun k y hy a ha => ?_, by linarith, by linarith [h.discount], fun k y hy => ?_⟩
  · -- l.h.c.: `yₙ = max{(1 − δ)kₙ, min{y, (1 + α)kₙ}}`
    have hval := (continuous_subtype_val.tendsto k).comp hks
    refine ⟨0, fun n => ⟨max ((1 - δ) * (ks n).1) (min y.1 ((1 + α) * (ks n).1)),
      le_max_of_le_left (mul_nonneg (by linarith) (ks n).2.out)⟩,
      fun n _ => ⟨le_max_left _ _, max_le (mul_le_mul_of_nonneg_right (by linarith)
        (ks n).2.out) (min_le_right _ _)⟩, ?_⟩
    have hlim := (hval.const_mul (1 - δ)).max ((tendsto_const_nhds (x := y.1)).min
      (hval.const_mul (1 + α)))
    rw [min_eq_left hy.2, max_eq_right hy.1] at hlim
    exact tendsto_subtype_rng.2 hlim
  · -- u.h.c.: the `yₙ` stay in a compact set
    have hval := (continuous_subtype_val.tendsto k).comp hks
    obtain ⟨B, hB⟩ := hval.bddAbove_range
    have hK : ∀ n, ys n ∈ Subtype.val ⁻¹' Icc (0 : ℝ) ((1 + α) * B) := fun n =>
      ⟨(ys n).2, (hys n).2.trans (mul_le_mul_of_nonneg_left
        (show (ks n).1 ≤ B from hB ⟨n, rfl⟩) (by linarith))⟩
    obtain ⟨y, -, φ, hφ, hlim⟩ := (hemb.isCompact_preimage isCompact_Icc).tendsto_subseq hK
    have hyl := (continuous_subtype_val.tendsto y).comp hlim
    have hkl := hval.comp hφ.tendsto_atTop
    refine ⟨y, ⟨?_, ?_⟩, φ, hφ, hlim⟩
    · exact le_of_tendsto_of_tendsto (hkl.const_mul (1 - δ)) hyl
        (Eventually.of_forall fun n => (hys (φ n)).1)
    · exact le_of_tendsto_of_tendsto hyl (hkl.const_mul (1 + α))
        (Eventually.of_forall fun n => (hys (φ n)).2)
  · -- the graph is a cone
    have h1 := hy.1
    have h2 := hy.2
    simp only [csmul, smul_eq_mul]
    exact ⟨by nlinarith, by nlinarith⟩
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg y.2.out, abs_of_nonneg k.2.out]
    exact hy.2

/-- On the graph, `|F(k, y)| ≤ Ck`. -/
theorem crs_F_bound (h : CRSInvHyp Fk p q δ α β) :
    ∃ C, 0 ≤ C ∧ ∀ k : CapStock, ∀ y ∈ crsΓ δ α k, |Fk k.1 y.1| ≤ C * k.1 := by
  have hδ := h.δ_lt
  have hδ0 := h.δ_pos
  have hα := h.α_pos
  have hc : ContinuousOn (Fk 1) (Icc (1 - δ) (1 + α)) :=
    h.F_cont.comp (continuous_const.prodMk continuous_id).continuousOn fun θ hθ =>
      ⟨mem_Ici.2 zero_le_one, mem_Ici.2 (show (0 : ℝ) ≤ θ by linarith [hθ.1])⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 ⟨by linarith, by linarith⟩)
  refine ⟨C, hC0, fun k y hy => ?_⟩
  rcases eq_or_lt_of_le k.2.out with hk0 | hkpos
  · -- `k = 0` forces `y = 0`, and `F(0, 0) = 0`
    have hy0 : y.1 = 0 := le_antisymm (by have := hy.2; rw [← hk0] at this; linarith) y.2.out
    have hF00 : Fk 0 0 = 0 := by
      have := h.F_hom 0 0 0 le_rfl le_rfl le_rfl
      simpa using this
    rw [← hk0, hy0, hF00]
    simp
  · have hθ : y.1 / k.1 ∈ Icc (1 - δ) (1 + α) :=
      ⟨(le_div_iff₀ hkpos).2 hy.1, (div_le_iff₀ hkpos).2 hy.2⟩
    have e : Fk k.1 y.1 = k.1 * Fk 1 (y.1 / k.1) := by
      have := h.F_hom k.1 1 (y.1 / k.1) hkpos.le zero_le_one (by linarith [hθ.1])
      rwa [mul_one, mul_div_cancel₀ _ hkpos.ne'] at this
    rw [e, abs_mul, abs_of_pos hkpos, mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hC _ hθ) hkpos.le

/-- Assumption 4.11 holds. -/
theorem crs_assumption411 (h : CRSInvHyp Fk p q δ α β) :
    ∃ B, Assumption411 isCone_Ici (crsΓ δ α) (crsH Fk p q δ) β B := by
  obtain ⟨C, hC0, hC⟩ := crs_F_bound h
  have hδ := h.δ_lt
  refine ⟨p * C + q + 1, h.β_pos, h.β_lt, ?_, fun k y hy a ha => ?_,
    by nlinarith [h.p_nonneg, h.q_nonneg], fun k y hy => ?_⟩
  · have hmaps : MapsTo (fun pr : CapStock × CapStock => (pr.1.1, pr.2.1))
        (graph (crsΓ δ α)) (Set.Ici 0 ×ˢ Set.Ici 0) := fun pr _ => ⟨pr.1.2, pr.2.2⟩
    exact (continuousOn_const.mul (h.F_cont.comp ((continuous_subtype_val.comp
      continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
        hmaps)).sub (continuous_const.mul ((continuous_subtype_val.comp continuous_snd).sub
          (continuous_const.mul (continuous_subtype_val.comp continuous_fst)))).continuousOn
  · simp only [crsH, csmul, smul_eq_mul]
    rw [h.F_hom a k.1 y.1 ha k.2.out y.2.out]
    ring
  · have h1 := hC k y hy
    have hk := k.2.out
    have hy0 := y.2.out
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hk, abs_of_nonneg hy0]
    simp only [crsH]
    have h2 : |q * (y.1 - (1 - δ) * k.1)| ≤ q * (y.1 + k.1) := by
      rw [abs_mul, abs_of_nonneg h.q_nonneg]
      refine mul_le_mul_of_nonneg_left ?_ h.q_nonneg
      have := mul_nonneg h.δ_pos.le hk
      rw [abs_le]; constructor <;> nlinarith
    have h3 : |p * Fk k.1 y.1| ≤ p * C * k.1 := by
      rw [abs_mul, abs_of_nonneg h.p_nonneg, mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 h.p_nonneg
    calc |p * Fk k.1 y.1 - q * (y.1 - (1 - δ) * k.1)|
        ≤ |p * Fk k.1 y.1| + |q * (y.1 - (1 - δ) * k.1)| := abs_sub _ _
      _ ≤ p * C * k.1 + q * (y.1 + k.1) := add_le_add h3 h2
      _ ≤ (p * C + q + 1) * (k.1 + y.1) := by
          nlinarith [mul_nonneg (mul_nonneg h.p_nonneg hC0) hy0, h.q_nonneg]

/-- **Exercise 5.10a.** `v*` is homogeneous of degree one: `v*(ak) = av*(k)` for `a ≥ 0`. -/
theorem ex_5_10a (h : CRSInvHyp Fk p q δ α β) (k : CapStock) {a : ℝ} (ha : 0 ≤ a) :
    vstar (crsΓ δ α) (curryF (crsH Fk p q δ)) β (csmul isCone_Ici ha k) =
      (a : EReal) * vstar (crsΓ δ α) (curryF (crsH Fk p q δ)) β k := by
  obtain ⟨B, h411⟩ := crs_assumption411 h
  obtain ⟨v, hvH, hv⟩ := ex_4_6c_hom (crs_assumption410 h) h411
  rw [hv]
  beta_reduce
  rw [hvH.2.1 k a ha, EReal.coe_mul]

/-- A real solution of the functional equation in max form solves it in `R̄`. -/
theorem satisfiesFE_of_solvesFE {X : Type*} {Γ : X → Set X} {F : X × X → ℝ} {v : X → ℝ}
    (hv : SolvesFE Γ F β v) : SatisfiesFE Γ (curryF F) β fun x => (v x : EReal) := by
  intro x
  obtain ⟨⟨y, hy, hval⟩, hmax⟩ := hv x
  change (v x : EReal) = ⨆ y ∈ Γ x, ((curryF F x y : ℝ) : EReal) + (β : EReal) * (v y : EReal)
  refine le_antisymm ?_ (iSup₂_le fun z hz => ?_)
  · refine le_trans ?_ (le_biSup (fun z => ((curryF F x z : ℝ) : EReal) +
      (β : EReal) * (v z : EReal)) hy)
    rw [hval, curryF, ← EReal.coe_mul, ← EReal.coe_add]
  · rw [curryF, ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2 (hmax z hz)

/-- **Exercise 5.10b.** The functional equation is invariant under rescaling: if `v` solves it,
so does `k ↦ v(ak)/a` for `a > 0`. -/
theorem solvesFE_rescale (h : CRSInvHyp Fk p q δ α β) {v : CapStock → ℝ}
    (hv : SolvesFE (crsΓ δ α) (crsH Fk p q δ) β v) {a : ℝ} (ha : 0 < a) :
    SolvesFE (crsΓ δ α) (crsH Fk p q δ) β fun k => v (csmul isCone_Ici ha.le k) / a := by
  have hhom : ∀ (k y : CapStock) (b : ℝ) (hb : 0 ≤ b),
      crsH Fk p q δ (csmul isCone_Ici hb k, csmul isCone_Ici hb y) = b * crsH Fk p q δ (k, y) :=
    fun k y b hb => by
      simp only [crsH, csmul, smul_eq_mul]
      rw [h.F_hom b k.1 y.1 hb k.2.out y.2.out]; ring
  have hcone : ∀ (k y : CapStock) (b : ℝ) (hb : 0 ≤ b), y ∈ crsΓ δ α k →
      csmul isCone_Ici hb y ∈ crsΓ δ α (csmul isCone_Ici hb k) := fun k y b hb hy => by
    simp only [crsΓ, csmul, smul_eq_mul, mem_ofPred_eq] at hy ⊢
    exact ⟨by nlinarith [hy.1], by nlinarith [hy.2]⟩
  have hinv : ∀ y : CapStock, csmul isCone_Ici ha.le (csmul isCone_Ici (inv_pos.2 ha).le y) = y :=
    fun y => Subtype.ext (by simp only [csmul, smul_eq_mul]; field_simp)
  intro k
  obtain ⟨⟨y', hy', hval⟩, hmax⟩ := hv (csmul isCone_Ici ha.le k)
  set y := csmul isCone_Ici (inv_pos.2 ha).le y'
  have hy : y ∈ crsΓ δ α k := by
    have := hcone _ y' a⁻¹ (inv_pos.2 ha).le hy'
    have hk : csmul isCone_Ici (inv_pos.2 ha).le (csmul isCone_Ici ha.le k) = k :=
      Subtype.ext (by simp only [csmul, smul_eq_mul]; field_simp)
    rwa [hk] at this
  refine ⟨⟨y, hy, ?_⟩, fun z hz => ?_⟩
  · beta_reduce
    rw [hval, ← hinv y', hhom k y a ha.le, hinv y']
    field_simp
  · beta_reduce
    have := hmax _ (hcone k z a ha.le hz)
    rw [hhom k z a ha.le] at this
    rw [le_div_iff₀ ha]
    have e : (crsH Fk p q δ (k, z) + β * (v (csmul isCone_Ici ha.le z) / a)) * a =
        a * crsH Fk p q δ (k, z) + β * v (csmul isCone_Ici ha.le z) := by field_simp
    rw [e]
    exact this

/-- **Exercise 5.10b.** Every solution of the functional equation with `|v(k)| ≤ Ck` equals
`v*`, and so is homogeneous of degree one. -/
theorem ex_5_10b (h : CRSInvHyp Fk p q δ α β) {v : CapStock → ℝ}
    (hv : SolvesFE (crsΓ δ α) (crsH Fk p q δ) β v) {C : ℝ} (hC : ∀ k : CapStock, |v k| ≤ C * k.1) :
    (fun k => (v k : EReal)) = vstar (crsΓ δ α) (curryF (crsH Fk p q δ)) β ∧
      ∀ (k : CapStock) (a : ℝ) (ha : 0 ≤ a), v (csmul isCone_Ici ha k) = a * v k := by
  obtain ⟨B, h411⟩ := crs_assumption411 h
  have h410 := crs_assumption410 h
  obtain ⟨h41, h42⟩ := ex_4_6b h410 h411
  have hαβ : 0 ≤ (1 + α) * β := mul_nonneg (by linarith [h.α_pos]) h.β_pos.le
  have hαβ1 : (1 + α) * β < 1 := by linarith [h.discount]
  have heq : (fun k => (v k : EReal)) = vstar (crsΓ δ α) (curryF (crsH Fk p q δ)) β := by
    refine theorem_4_3 h.β_pos.le h41 h42 (satisfiesFE_of_solvesFE hv) fun x₀ x hx => ?_
    have hb : Tendsto (fun n => β ^ n * v (x n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n => |C| * ‖x₀.1‖ * ((1 + α) * β) ^ n)
        (fun n => ?_) ?_
      · have hxn := ex_4_6a h410 hx n
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h.β_pos.le n)]
        have hvx : |v (x n)| ≤ |C| * ‖(x n).1‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg (x n).2.out]
          exact (hC _).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (x n).2.out)
        calc β ^ n * |v (x n)| ≤ β ^ n * (|C| * ((1 + α) ^ n * ‖x₀.1‖)) :=
              mul_le_mul_of_nonneg_left (hvx.trans (mul_le_mul_of_nonneg_left hxn
                (abs_nonneg C))) (pow_nonneg h.β_pos.le n)
          _ = |C| * ‖x₀.1‖ * ((1 + α) * β) ^ n := by rw [mul_pow]; ring
      · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hαβ hαβ1).const_mul (|C| * ‖x₀.1‖)
    simpa only [EReal.coe_mul, EReal.coe_zero] using EReal.tendsto_coe.2 hb
  refine ⟨heq, fun k a ha => ?_⟩
  have h1 := congrFun heq (csmul isCone_Ici ha k)
  have h2 := congrFun heq k
  rw [ex_5_10a h k ha, ← h2, ← EReal.coe_mul] at h1
  exact EReal.coe_injective h1

/-- **Exercise 5.10c.** Let `v` be the fixed point of Theorem 4.13 and `A = v(1)`. Then
`v(k) = Ak`; `A = max_θ [pF(1, θ) − q(θ − (1 − δ)) + βAθ]`, attained at some
`θ ∈ [1 − δ, 1 + α]`; `y = θk` is optimal at every `k`; `v = v*`; and when `p > 0` and
`F(1, ·)` is strictly concave on `[1 − δ, 1 + α]`, `θ` is the only optimal growth factor. -/
theorem ex_5_10c (h : CRSInvHyp Fk p q δ α β) :
    ∃ v : CapStock → ℝ, ∃ A θ : ℝ, θ ∈ Icc (1 - δ) (1 + α) ∧
      (∀ k : CapStock, v k = A * k.1) ∧
      (fun k => (v k : EReal)) = vstar (crsΓ δ α) (curryF (crsH Fk p q δ)) β ∧
      A = p * Fk 1 θ - q * (θ - (1 - δ)) + β * A * θ ∧
      (∀ θ' ∈ Icc (1 - δ) (1 + α), p * Fk 1 θ' - q * (θ' - (1 - δ)) + β * A * θ' ≤ A) ∧
      (0 < p → StrictConcaveOn ℝ (Icc (1 - δ) (1 + α)) (Fk 1) →
        ∀ θ' ∈ Icc (1 - δ) (1 + α), p * Fk 1 θ' - q * (θ' - (1 - δ)) + β * A * θ' = A →
          θ' = θ) := by
  obtain ⟨B, h411⟩ := crs_assumption411 h
  have h410 := crs_assumption410 h
  obtain ⟨v, hvH, hv, -, -, hG, -⟩ := theorem_4_13 h410 h411
  have hδ := h.δ_lt
  have hα := h.α_pos
  set one : CapStock := ⟨1, mem_Ici.2 zero_le_one⟩
  set A := v one
  have hlin : ∀ k : CapStock, v k = A * k.1 := fun k => by
    have := hvH.2.1 one k.1 k.2.out
    have hk : csmul isCone_Ici k.2.out one = k := Subtype.ext (by simp [csmul, one])
    rw [hk] at this
    rw [this, mul_comm]
  -- the maximizer at `k = 1`
  obtain ⟨y, hy⟩ := (hG one).1
  have hθ : y.1 ∈ Icc (1 - δ) (1 + α) := by
    have := hy.1; simp only [crsΓ, one, mul_one, mem_ofPred_eq] at this; exact this
  have hvx : ∀ x, v x = maxValue (obj (crsH Fk p q δ) β v) (crsΓ δ α) x := fun x =>
    (congrFun hv x).symm
  have hFE : ∀ z ∈ crsΓ δ α one, obj (crsH Fk p q δ) β v (one, z) ≤ v one := fun z hz => by
    rw [hvx one]
    exact le_maxValue (continuousOn_obj' h411 hvH.1) (h410.compact one) hz
  have hval : v one = obj (crsH Fk p q δ) β v (one, y) := by rw [hvx one]; exact hy.2.symm
  have hobj : ∀ z : CapStock, obj (crsH Fk p q δ) β v (one, z) =
      p * Fk 1 z.1 - q * (z.1 - (1 - δ)) + β * A * z.1 := fun z => by
    simp only [obj, crsH, one, hlin z, mul_one]; ring
  refine ⟨v, A, y.1, hθ, hlin, crs_fixed_eq_vstar h410 h411 hvH hv, ?_, fun θ' hθ' => ?_,
    fun hp hFs θ' hθ' heq => ?_⟩
  · rw [← hobj]; exact hval
  · have := hFE ⟨θ', mem_Ici.2 (by linarith [hθ'.1])⟩
      (by simp only [crsΓ, one, mul_one, mem_ofPred_eq]; exact hθ')
    rwa [hobj] at this
  · -- strict concavity of the objective in `θ` makes the maximizer unique
    by_contra hne
    have hs := hFs.2 hθ hθ' (Ne.symm hne) (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul] at hs
    have hmid : (1 / 2 : ℝ) • y.1 + (1 / 2 : ℝ) • θ' ∈ Icc (1 - δ) (1 + α) :=
      (convex_Icc _ _) hθ hθ' (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hmid
    have h1 := hFE ⟨1 / 2 * y.1 + 1 / 2 * θ', mem_Ici.2 (by linarith [hmid.1])⟩
      (by simp only [crsΓ, one, mul_one, mem_ofPred_eq]; exact hmid)
    rw [hobj] at h1
    have h2 : p * Fk 1 y.1 - q * (y.1 - (1 - δ)) + β * A * y.1 = A := by
      rw [← hobj]; exact hval.symm
    simp only at h1
    nlinarith [mul_lt_mul_of_pos_left hs hp]

end StokeyLucasPrescott.DeterministicApplications
