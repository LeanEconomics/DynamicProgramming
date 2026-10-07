/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPTransformations.EpsteinZin
import ADPTransformations.FactoredDP

/-!
# Epstein–Zin savings with iid endowments

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.3.3 (pp. 178–181).

Wealth `w ∈ W` and endowment `e ∈ E` are finite, the endowment is iid with distribution `φ`, and
the Bellman equation is (5.31). It is the Epstein–Zin model of §5.1.3 on `X = W × E`, `A = W`
(`toEZ`). The FDP `(V, F, V̂, 𝔾)` has `(Fv)(w) = {∑_e v(w, e)^ν φ(e)}^{1/ν}`, `V̂ = F(V)`, and
`(G_σ h)(w, e) = {(1 − β)r(w, σ(w, e), e)^α + βh(σ(w, e))^α}^{1/α}` (5.32).

* The FDP is order preserving (`fdp_isOrderPreserving`); a greatest `G_σ h` is the pointwise
  maximizer (5.33).
* **Exercise 5.3.1**: the primary ADP has the policy operators (5.34), those of the Epstein–Zin
  model, so it is isomorphic to `(V, 𝕋_EZ)` under the identity.
* **Exercise 5.3.2**: the subordinate ADP has the policy operators (5.35), acting on functions of
  `w` alone.
* `section_5_3_3`: the fundamental optimality properties hold for both ADPs (Proposition 5.1.13
  and Theorem 5.2.13); a policy satisfying (5.33) at `h = v̂*` is optimal for (5.31); and HPI on
  the subordinate ADP reaches `v̂*` in finitely many steps, which is Algorithm 5.1.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

/-- Power means are order preserving: for weights `φ` summing to one and `p ≠ 0`,
`u ≤ u'` implies `(∑ u^p φ)^{1/p} ≤ (∑ u'^p φ)^{1/p}` on positive vectors. -/
theorem powerSum_pos {ι : Type*} [Fintype ι] {φ : ι → ℝ} (hφ0 : ∀ i, 0 ≤ φ i)
    (hφ1 : ∑ i, φ i = 1) {p : ℝ} {u : ι → ℝ} (hu : ∀ i, 0 < u i) : 0 < ∑ i, u i ^ p * φ i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < φ j := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have : ∑ i, φ i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (hφ0 i)
    rw [hφ1] at this
    exact one_ne_zero this
  exact Finset.sum_pos' (fun i _ => mul_nonneg (Real.rpow_pos_of_pos (hu i) _).le (hφ0 i))
    ⟨j, Finset.mem_univ _, mul_pos (Real.rpow_pos_of_pos (hu j) _) hj⟩

theorem powerMean_mono {ι : Type*} [Fintype ι] {φ : ι → ℝ} (hφ0 : ∀ i, 0 ≤ φ i)
    (hφ1 : ∑ i, φ i = 1) {p : ℝ} (hp : p ≠ 0) {u u' : ι → ℝ} (hu : ∀ i, 0 < u i) (hle : u ≤ u') :
    (∑ i, u i ^ p * φ i) ^ p⁻¹ ≤ (∑ i, u' i ^ p * φ i) ^ p⁻¹ := by
  have hu' : ∀ i, 0 < u' i := fun i => (hu i).trans_le (hle i)
  have hS := powerSum_pos hφ0 hφ1 (p := p) hu
  have hS' := powerSum_pos hφ0 hφ1 (p := p) hu'
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · have h1 : ∑ i, u' i ^ p * φ i ≤ ∑ i, u i ^ p * φ i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos (hu i) (hle i) hneg.le) (hφ0 i)
    exact Real.rpow_le_rpow_of_nonpos hS' h1 (inv_lt_zero.2 hneg).le
  · have h1 : ∑ i, u i ^ p * φ i ≤ ∑ i, u' i ^ p * φ i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (hu i).le (hle i) hpos.le) (hφ0 i)
    exact Real.rpow_le_rpow hS.le h1 (inv_nonneg.2 hpos.le)

/-- `t ↦ {(1 − β)c + βt^α}^{1/α}` is order preserving on `(0, ∞)`. -/
theorem aggr_mono {β c α : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hc : 0 < c) (hα : α ≠ 0) {t t' : ℝ}
    (ht : 0 < t) (hle : t ≤ t') :
    ((1 - β) * c + β * t ^ α) ^ α⁻¹ ≤ ((1 - β) * c + β * t' ^ α) ^ α⁻¹ := by
  have hk : 0 < (1 - β) * c := mul_pos (sub_pos.2 hβ1) hc
  have hpos : ∀ s : ℝ, 0 < s → 0 < (1 - β) * c + β * s ^ α := fun s hs =>
    add_pos_of_pos_of_nonneg hk (mul_nonneg hβ0 (Real.rpow_pos_of_pos hs _).le)
  rcases lt_or_gt_of_ne hα with hneg | hposα
  · have h1 : (1 - β) * c + β * t' ^ α ≤ (1 - β) * c + β * t ^ α :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht hle hneg.le) hβ0)
    exact Real.rpow_le_rpow_of_nonpos (hpos t' (ht.trans_le hle)) h1 (inv_lt_zero.2 hneg).le
  · have h1 : (1 - β) * c + β * t ^ α ≤ (1 - β) * c + β * t' ^ α :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.le hle hposα.le) hβ0)
    exact Real.rpow_le_rpow (hpos t ht).le h1 (inv_nonneg.2 hposα.le)

/-- The Epstein–Zin savings model (5.31): wealth `W`, endowments `E` drawn iid from `φ`,
feasible next-period wealth `Γ(w, e)` and reward `r(w, w', e) > 0`. -/
structure EZSavings (W E : Type*) [Fintype W] [Fintype E] where
  /-- the feasible next-period wealth levels -/
  Γ : W × E → Finset W
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the reward `r(w, w', e)` -/
  r : W → W → E → ℝ
  r_pos : ∀ w w' e, 0 < r w w' e
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the endowment distribution -/
  φ : E → ℝ
  φ_nonneg : ∀ e, 0 ≤ φ e
  φ_sum : ∑ e, φ e = 1
  α : ℝ
  ν : ℝ
  α_ne : α ≠ 0
  ν_ne : ν ≠ 0
  c₁ : ℝ
  c₂ : ℝ
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₁_lt : ∀ x, ∀ w' ∈ Γ x, c₁ < r x.1 w' x.2 ^ α
  lt_c₂ : ∀ x, ∀ w' ∈ Γ x, r x.1 w' x.2 ^ α < c₂

namespace EZSavings

variable {W E : Type*} [Fintype W] [Fintype E] [DecidableEq W] (S : EZSavings W E)

/-- The model as an Epstein–Zin model (5.10) on `X = W × E`, `A = W`, with
`P((w, e), w', (w'', e')) = 𝟙{w'' = w'}φ(e')`. -/
noncomputable def toEZ : EZModel (W × E) W where
  Γ := S.Γ
  Γ_nonempty := S.Γ_nonempty
  r x w' := S.r x.1 w' x.2
  r_pos x w' := S.r_pos x.1 w' x.2
  β := S.β
  β_nonneg := S.β_nonneg
  β_lt_one := S.β_lt_one
  P _ w' x' := if x'.1 = w' then S.φ x'.2 else 0
  P_nonneg _ _ x' := by
    split_ifs
    · exact S.φ_nonneg _
    · exact le_rfl
  P_sum _ w' := by
    rw [Fintype.sum_prod_type_right]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact S.φ_sum
  α := S.α
  ν := S.ν
  α_ne := S.α_ne
  ν_ne := S.ν_ne
  c₁ := S.c₁
  c₂ := S.c₂
  c₁_pos := S.c₁_pos
  c₁_lt_c₂ := S.c₁_lt_c₂
  c₁_lt := S.c₁_lt
  lt_c₂ := S.lt_c₂

/-- `(Fv)(w) = {∑_e v(w, e)^ν φ(e)}^{1/ν}`. -/
noncomputable def Fraw (v : W × E → ℝ) (w : W) : ℝ := (∑ e, v (w, e) ^ S.ν * S.φ e) ^ S.ν⁻¹

/-- `(G_σ h)(w, e) = {(1 − β)r(w, σ(w, e), e)^α + βh(σ(w, e))^α}^{1/α}` (5.32). -/
noncomputable def Graw (σ : S.toEZ.Policy) (h : W → ℝ) (x : W × E) : ℝ :=
  ((1 - S.β) * S.r x.1 (σ.1 x) x.2 ^ S.α + S.β * h (σ.1 x) ^ S.α) ^ S.α⁻¹

theorem Pσ_eq (σ : S.toEZ.Policy) (v : W × E → ℝ) (x : W × E) :
    S.toEZ.Pσ σ (fun x' => v x' ^ S.ν) x = ∑ e, v (σ.1 x, e) ^ S.ν * S.φ e := by
  change ∑ x', v x' ^ S.ν * (if x'.1 = σ.1 x then S.φ x'.2 else 0) = _
  rw [Fintype.sum_prod_type_right]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Exercise 5.3.1** (p. 179): `G_σ ∘ F = T_σ`, the Epstein–Zin policy operator (5.34). -/
theorem exercise_5_3_1 (σ : S.toEZ.Policy) (v : W × E → ℝ) :
    S.Graw σ (S.Fraw v) = S.toEZ.Tσ σ v := by
  funext x
  have h := S.Pσ_eq σ v x
  change ((1 - S.β) * S.r x.1 (σ.1 x) x.2 ^ S.α + S.β * S.Fraw v (σ.1 x) ^ S.α) ^ S.α⁻¹ =
    ((1 - S.β) * S.r x.1 (σ.1 x) x.2 ^ S.α +
      S.β * (S.toEZ.Pσ σ (fun x' => v x' ^ S.ν) x ^ S.ν⁻¹) ^ S.α) ^ S.α⁻¹
  rw [h]
  rfl

/-- `V̂ = F(V)`. -/
def Vhat : Set (W → ℝ) := {h | ∃ v ∈ S.toEZ.V, S.Fraw v = h}

theorem Fraw_pos {v : W × E → ℝ} (hv : v ∈ S.toEZ.V) (w : W) : 0 < S.Fraw v w :=
  Real.rpow_pos_of_pos (powerSum_pos S.φ_nonneg S.φ_sum (u := fun e => v (w, e))
    fun e => hv.1 (w, e)) _

theorem Graw_mem (σ : S.toEZ.Policy) {h : W → ℝ} (hh : h ∈ S.Vhat) : S.Graw σ h ∈ S.toEZ.V := by
  obtain ⟨v, hv, rfl⟩ := hh
  rw [S.exercise_5_3_1]
  exact S.toEZ.Tσ_mem σ hv

/-- The FDP `(V, F, V̂, 𝔾)` of §5.3.3. -/
noncomputable def fdp : FDP S.toEZ.V S.Vhat S.toEZ.Policy where
  F v := ⟨S.Fraw v.1, v.1, v.2, rfl⟩
  G σ h := ⟨S.Graw σ h.1, S.Graw_mem σ h.2⟩
  greatest h := by
    choose σ hσ hmax using fun x => Finset.exists_max_image (S.Γ x)
      (fun w' => ((1 - S.β) * S.r x.1 w' x.2 ^ S.α + S.β * h.1 w' ^ S.α) ^ S.α⁻¹)
      (S.Γ_nonempty x)
    exact ⟨⟨σ, hσ⟩, fun τ x => hmax x (τ.1 x) (τ.2 x)⟩
  nonempty := S.toEZ.nonempty_policy

theorem Vhat_pos {h : W → ℝ} (hh : h ∈ S.Vhat) (w : W) : 0 < h w := by
  obtain ⟨v, hv, rfl⟩ := hh
  exact S.Fraw_pos hv w

/-- The FDP of §5.3.3 is order preserving. -/
theorem fdp_isOrderPreserving : S.fdp.IsOrderPreserving := by
  refine ⟨fun v v' hle w => ?_, fun σ h h' hle x => ?_⟩
  · exact powerMean_mono S.φ_nonneg S.φ_sum S.ν_ne (fun e => v.2.1 (w, e)) fun e => hle (w, e)
  · exact aggr_mono S.β_nonneg S.β_lt_one (Real.rpow_pos_of_pos (S.r_pos _ _ _) _) S.α_ne
      (S.Vhat_pos h.2 _) (hle _)

theorem fdp_monotonic : S.fdp.Monotonic := Or.inl S.fdp_isOrderPreserving

/-- The primary ADP coincides with the Epstein–Zin ADP `(V, 𝕋_EZ)`: they are isomorphic under the
identity (Exercise 5.3.1). -/
theorem primary_isIsomorphic :
    (S.fdp.primary S.fdp_monotonic).IsIsomorphic S.toEZ.adp (OrderIso.refl _) := fun σ v =>
  Subtype.ext (S.exercise_5_3_1 σ v.1)

/-- **Exercise 5.3.2** (p. 180): the subordinate policy operators (5.35),
`(T̂_σ h)(w) = {∑_e {(1 − β)r(w, σ(w, e), e)^α + βh(σ(w, e))^α}^{ν/α} φ(e)}^{1/ν}`. -/
theorem exercise_5_3_2 (σ : S.toEZ.Policy) (h : S.Vhat) (w : W) :
    ((S.fdp.sub S.fdp_monotonic).T σ h).1 w =
      (∑ e, ((1 - S.β) * S.r w (σ.1 (w, e)) e ^ S.α + S.β * h.1 (σ.1 (w, e)) ^ S.α) ^
        (S.ν / S.α) * S.φ e) ^ S.ν⁻¹ := by
  change (∑ e, S.Graw σ h.1 (w, e) ^ S.ν * S.φ e) ^ S.ν⁻¹ = _
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Graw, ← Real.rpow_mul, div_eq_inv_mul]
  exact add_nonneg (mul_nonneg (sub_pos.2 S.β_lt_one).le
    (Real.rpow_pos_of_pos (S.r_pos _ _ _) _).le)
    (mul_nonneg S.β_nonneg (Real.rpow_pos_of_pos (S.Vhat_pos h.2 _) _).le)

/-- §5.3.3 (pp. 180–181): the fundamental optimality properties hold for the Epstein–Zin savings
model and for its subordinate ADP; any `σ` satisfying (5.33) at `h = v̂*` is optimal; and HPI on
the subordinate ADP reaches `v̂*` in finitely many steps from every `ĥ ∈ V̂_U` (Algorithm 5.1). -/
theorem section_5_3_3 :
    ∃ (hw : S.toEZ.adp.WellPosed) (hw' : (S.fdp.sub S.fdp_monotonic).WellPosed),
      S.toEZ.adp.FundamentalOptimality hw ∧
      (S.fdp.sub S.fdp_monotonic).FundamentalOptimality hw' ∧
      (∀ hstar σ, (S.fdp.sub S.fdp_monotonic).IsValueFunction hstar →
        (∀ x, ∀ w' ∈ S.Γ x, ((1 - S.β) * S.r x.1 w' x.2 ^ S.α + S.β * hstar.1 w' ^ S.α) ^ S.α⁻¹ ≤
          ((1 - S.β) * S.r x.1 (σ.1 x) x.2 ^ S.α + S.β * hstar.1 (σ.1 x) ^ S.α) ^ S.α⁻¹) →
        S.toEZ.adp.IsOptimal hw σ) ∧
      ∀ g, (S.fdp.sub S.fdp_monotonic).IsSelector g → ∀ h ∈ (S.fdp.sub S.fdp_monotonic).VU,
        ∃ n, (S.fdp.sub S.fdp_monotonic).IsValueFunction
          (((S.fdp.sub S.fdp_monotonic).howard hw' g)^[n] h) := by
  have hm := S.fdp_monotonic
  have hP := S.fdp_isOrderPreserving
  have hiso := S.primary_isIsomorphic
  obtain ⟨hw, hFO, -⟩ := S.toEZ.proposition_5_1_13
  have hwp : (S.fdp.primary hm).WellPosed := hiso.wellPosed_iff.2 hw
  have hosP : (S.fdp.primary hm).IsOrderStable := hiso.orderStable_iff.2 S.toEZ.adp_isOrderStable
  have hosS : (S.fdp.sub hm).IsOrderStable := (FDP.lemma_5_2_12 hm).2.1.2 hosP
  have hw' : (S.fdp.sub hm).WellPosed := hosS.wellPosed
  have hFOp : (S.fdp.primary hm).FundamentalOptimality hwp :=
    (hiso.fundamentalOptimality_iff hwp hw).2 hFO
  have key := FDP.theorem_5_2_13 hm hP hwp hw'
  have hFOs := key.1.1 hFOp
  have hfin : (S.fdp.sub hm).IsFinite := by
    have := S.toEZ.finite_policy
    exact Set.finite_range _
  have hreg : (S.fdp.sub hm).Regular := FDP.sub_regular hm hP.1
  refine ⟨hw, hw', hFO, hFOs, fun hstar σ hv hσ => ?_, fun g hg h hh => ?_⟩
  · have hopt := (key.2 hFOp).2.1 hstar σ hv (le_antisymm (S.fdp.G_le_Gsup σ hstar)
      fun x => ?_)
    · exact (hiso.isOptimal_iff hwp hw σ).1 hopt
    · exact hσ x _ ((S.fdp.gsel hstar).2 x)
  · obtain ⟨-, hn⟩ := ADP.fundamentalOptimality_of_finite hosS hreg hfin
    exact hn g hg h hh

end EZSavings

end SargentStachurski.ADPTransformations
