/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPTransformations.EZScalar
import ADPTransformations.DuReflection
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Epstein–Zin optimality

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §5.1.3 (pp. 157–160).

The finite-state Epstein–Zin model (5.10) has policy operators (5.11),
`T_σ v = {(1 − β)r_σ^α + β(L_σ v)^α}^{1/α}` with
`(L_σ v)(x) = (∑_{x'} v(x')^ν P(x, σ(x), x'))^{1/ν}`, for nonzero `α, ν`. With `θ = ν/α`, the
auxiliary ADP (5.13) on `V̂ = [v₁, v₂]` is
`T̂_σ v = {(1 − β)r_σ^α + β(P_σ v)^{1/θ}}^θ`, and `Fv = v^ν` links the two (5.12).

* **Exercise 5.1.9**: `v₁ ≪ T̂_σ v₁` and `T̂_σ v₂ ≪ v₂`.
* **Exercise 5.1.10**: `T̂_σ` is convex on `V̂` if `0 < θ ≤ 1` and concave if `θ < 0` or `1 ≤ θ`.
* **Lemma 5.1.11**: the fundamental max- and min-optimality properties hold for `(V̂, 𝕋̂_EZ)`,
  with VFI, OPI and HPI converging in both senses (Theorem 4.1.11 and its reflection).
* **Exercise 5.1.11**: `F ∘ T_σ = T̂_σ ∘ F` on `V`.
* **Lemma 5.1.12**: `(V, 𝕋_EZ)` and `(V̂, 𝕋̂_EZ)` are isomorphic if `ν > 0` and anti-isomorphic if
  `ν < 0`.
* **Proposition 5.1.13**: the fundamental optimality properties hold for `(V, 𝕋_EZ)`, and VFI,
  OPI and HPI all converge, without irreducibility of `P_σ`.

The book takes `v₁ = m₁ ∧ m₂`, `v₂ = m₁ ∨ m₂` with `m₁ = (min r^α − ε)^θ` and
`m₂ = (max r^α + ε)^θ`; here `m₁ = c₁^θ`, `m₂ = c₂^θ` for any `0 < c₁ < r^α < c₂` on the feasible
pairs, which includes that choice.
-/

open Set Function Filter Topology

namespace SargentStachurski.ADPTransformations

/-- The supremum norm of `ℝ^ι` is a lattice norm. -/
theorem hasSolidNorm_pi {ι : Type*} [Fintype ι] : HasSolidNorm (ι → ℝ) :=
  ⟨fun f g h => (pi_norm_le_iff_of_nonneg (norm_nonneg g)).2 fun i => by
    rw [Real.norm_eq_abs]
    exact (show |f i| ≤ |g i| from h i).trans ((Real.norm_eq_abs (g i)).symm.trans_le
      (norm_le_pi_norm g i))⟩

attribute [local instance] hasSolidNorm_pi

/-- On a finite set, a positive function has a positive lower bound: some `ε ∈ (0, 1)` has
`εd ≤ u(x)` for all `x`. -/
theorem exists_eps_mul_le {X : Type*} [Finite X] (u : X → ℝ) (hu : ∀ x, 0 < u x) {d : ℝ}
    (hd : 0 < d) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x, ε * d ≤ u x := by
  have := Fintype.ofFinite X
  obtain ⟨δ, hδ, hδu⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x, δ ≤ u x := by
    rcases (Finset.univ : Finset X).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun x =>
        absurd (Finset.mem_univ x) (by rw [he]; exact Finset.notMem_empty x)⟩
    · exact ⟨Finset.univ.inf' hne u, (Finset.lt_inf'_iff hne).2 fun x _ => hu x,
        fun x => Finset.inf'_le u (Finset.mem_univ x)⟩
  refine ⟨min (1 / 2) (δ / d), lt_min (by norm_num) (div_pos hδ hd),
    (min_le_left _ _).trans_lt (by norm_num), fun x => ?_⟩
  calc min (1 / 2) (δ / d) * d ≤ δ / d * d := mul_le_mul_of_nonneg_right (min_le_right _ _) hd.le
    _ = δ := div_mul_cancel₀ δ hd.ne'
    _ ≤ u x := hδu x

/-- The finite-state Epstein–Zin model (5.10), with bounds `c₁ < r^α < c₂` on the feasible
pairs. -/
structure EZModel (X A : Type*) [Fintype X] where
  /-- the feasible correspondence -/
  Γ : X → Finset A
  Γ_nonempty : ∀ x, (Γ x).Nonempty
  /-- the (strictly positive) reward -/
  r : X → A → ℝ
  r_pos : ∀ x a, 0 < r x a
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the transition probabilities -/
  P : X → A → X → ℝ
  P_nonneg : ∀ x a x', 0 ≤ P x a x'
  P_sum : ∀ x a, ∑ x', P x a x' = 1
  /-- `α = 1 − 1/ψ` -/
  α : ℝ
  /-- `ν = 1 − γ` -/
  ν : ℝ
  α_ne : α ≠ 0
  ν_ne : ν ≠ 0
  /-- a lower bound for `r^α` -/
  c₁ : ℝ
  /-- an upper bound for `r^α` -/
  c₂ : ℝ
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₁_lt : ∀ x, ∀ a ∈ Γ x, c₁ < r x a ^ α
  lt_c₂ : ∀ x, ∀ a ∈ Γ x, r x a ^ α < c₂

namespace EZModel

variable {X A : Type*} [Fintype X] (M : EZModel X A)

/-- `θ = ν/α`. -/
noncomputable def θ : ℝ := M.ν / M.α

theorem θ_ne : M.θ ≠ 0 := div_ne_zero M.ν_ne M.α_ne

/-- Feasible policies. -/
def Policy : Type _ := {σ : X → A // ∀ x, σ x ∈ M.Γ x}

theorem nonempty_policy : Nonempty M.Policy :=
  ⟨⟨fun x => (M.Γ_nonempty x).choose, fun x => (M.Γ_nonempty x).choose_spec⟩⟩

theorem finite_policy : Finite M.Policy := by
  classical
  refine Finite.of_injective (fun σ : M.Policy => fun x => (⟨σ.1 x, σ.2 x⟩ : M.Γ x)) ?_
  intro σ τ h
  apply Subtype.ext
  funext x
  have := congrFun h x
  simpa using congrArg Subtype.val this

theorem c₂_pos : 0 < M.c₂ := M.c₁_pos.trans M.c₁_lt_c₂

/-- `v₁ = m₁ ∧ m₂`, with `m₁ = c₁^θ`, `m₂ = c₂^θ`. -/
noncomputable def lo : ℝ := if 0 < M.θ then M.c₁ ^ M.θ else M.c₂ ^ M.θ

/-- `v₂ = m₁ ∨ m₂`. -/
noncomputable def hi : ℝ := if 0 < M.θ then M.c₂ ^ M.θ else M.c₁ ^ M.θ

theorem lo_pos : 0 < M.lo := by
  unfold lo; split_ifs
  · exact Real.rpow_pos_of_pos M.c₁_pos _
  · exact Real.rpow_pos_of_pos M.c₂_pos _

theorem hi_pos : 0 < M.hi := by
  unfold hi; split_ifs
  · exact Real.rpow_pos_of_pos M.c₂_pos _
  · exact Real.rpow_pos_of_pos M.c₁_pos _

theorem lo_lt_hi : M.lo < M.hi := by
  unfold lo hi; split_ifs with h
  · exact Real.rpow_lt_rpow M.c₁_pos.le M.c₁_lt_c₂ h
  · exact Real.rpow_lt_rpow_of_neg M.c₁_pos M.c₁_lt_c₂
      (lt_of_le_of_ne (not_lt.1 h) M.θ_ne)

/-- The constant function `v₁`. -/
noncomputable def a : X → ℝ := fun _ => M.lo

/-- The constant function `v₂`. -/
noncomputable def b : X → ℝ := fun _ => M.hi

theorem a_le_b : M.a ≤ M.b := fun _ => M.lo_lt_hi.le

/-- `(P_σ v)(x) = ∑_{x'} v(x')P(x, σ(x), x')`. -/
def Pσ (σ : M.Policy) (v : X → ℝ) (x : X) : ℝ := ∑ x', v x' * M.P x (σ.1 x) x'

theorem Pσ_const (σ : M.Policy) (c : ℝ) (x : X) : M.Pσ σ (fun _ => c) x = c := by
  rw [Pσ, ← Finset.mul_sum, M.P_sum, mul_one]

theorem Pσ_mono (σ : M.Policy) {v w : X → ℝ} (h : v ≤ w) (x : X) : M.Pσ σ v x ≤ M.Pσ σ w x :=
  Finset.sum_le_sum fun x' _ => mul_le_mul_of_nonneg_right (h x') (M.P_nonneg _ _ _)

theorem Pσ_combo (σ : M.Policy) (v w : X → ℝ) (s t : ℝ) (x : X) :
    M.Pσ σ (s • v + t • w) x = s * M.Pσ σ v x + t * M.Pσ σ w x := by
  simp only [Pσ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x' _ => by ring

theorem Pσ_mem (σ : M.Policy) {v : X → ℝ} (hv : v ∈ Icc M.a M.b) (x : X) :
    M.lo ≤ M.Pσ σ v x ∧ M.Pσ σ v x ≤ M.hi :=
  ⟨(M.Pσ_const σ M.lo x).symm.le.trans (M.Pσ_mono σ hv.1 x),
    (M.Pσ_mono σ hv.2 x).trans (M.Pσ_const σ M.hi x).le⟩

theorem Pσ_pos (σ : M.Policy) {v : X → ℝ} (hv : v ∈ Icc M.a M.b) (x : X) : 0 < M.Pσ σ v x :=
  M.lo_pos.trans_le (M.Pσ_mem σ hv x).1

/-- The auxiliary policy operator (5.13), `T̂_σ v = {(1 − β)r_σ^α + β(P_σ v)^{1/θ}}^θ`. -/
noncomputable def That (σ : M.Policy) (v : X → ℝ) : X → ℝ :=
  fun x => EZ.f M.β M.θ (M.r x (σ.1 x) ^ M.α) (M.Pσ σ v x)

theorem rα_pos (x : X) (a : A) : 0 < M.r x a ^ M.α := Real.rpow_pos_of_pos (M.r_pos x a) _

theorem That_le (σ : M.Policy) {v w : X → ℝ} (hv : v ∈ Icc M.a M.b) (hw : w ∈ Icc M.a M.b)
    (h : v ≤ w) : M.That σ v ≤ M.That σ w := fun x =>
  EZ.f_monotoneOn M.β_nonneg M.β_lt_one (M.rα_pos x _) M.θ_ne (M.Pσ_pos σ hv x)
    (M.Pσ_pos σ hw x) (M.Pσ_mono σ h x)

/-- `v₁ < f(v₁)` and `f(v₂) < v₂` for `f(t) = ((1 − β)c + βt^{1/θ})^θ` with `c₁ < c < c₂`. -/
theorem lo_lt_f_hi {c : ℝ} (hc1 : M.c₁ < c) (hc2 : c < M.c₂) :
    M.lo < EZ.f M.β M.θ c M.lo ∧ EZ.f M.β M.θ c M.hi < M.hi := by
  have hβ1 := sub_pos.2 M.β_lt_one
  have hA : M.c₁ < (1 - M.β) * c + M.β * M.c₁ := by nlinarith [M.β_nonneg]
  have hB : (1 - M.β) * c + M.β * M.c₂ < M.c₂ := by nlinarith [M.β_nonneg]
  have hApos : 0 < (1 - M.β) * c + M.β * M.c₁ := M.c₁_pos.trans hA
  have hBpos : 0 < (1 - M.β) * c + M.β * M.c₂ :=
    add_pos_of_pos_of_nonneg (mul_pos hβ1 (M.c₁_pos.trans hc1)) (mul_nonneg M.β_nonneg M.c₂_pos.le)
  unfold lo hi
  split_ifs with hθ
  · rw [EZ.f_rpow M.θ_ne M.c₁_pos, EZ.f_rpow M.θ_ne M.c₂_pos]
    exact ⟨Real.rpow_lt_rpow M.c₁_pos.le hA hθ, Real.rpow_lt_rpow hBpos.le hB hθ⟩
  · have hneg : M.θ < 0 := lt_of_le_of_ne (not_lt.1 hθ) M.θ_ne
    rw [EZ.f_rpow M.θ_ne M.c₂_pos, EZ.f_rpow M.θ_ne M.c₁_pos]
    exact ⟨Real.rpow_lt_rpow_of_neg hBpos hB hneg, Real.rpow_lt_rpow_of_neg M.c₁_pos hA hneg⟩

/-- **Exercise 5.1.9** (p. 158): `v₁ ≪ T̂_σ v₁` and `T̂_σ v₂ ≪ v₂`. -/
theorem exercise_5_1_9 (σ : M.Policy) :
    (∀ x, M.a x < M.That σ M.a x) ∧ ∀ x, M.That σ M.b x < M.b x := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · change M.lo < EZ.f M.β M.θ _ (M.Pσ σ (fun _ => M.lo) x)
    rw [M.Pσ_const]
    exact (M.lo_lt_f_hi (M.c₁_lt x _ (σ.2 x)) (M.lt_c₂ x _ (σ.2 x))).1
  · change EZ.f M.β M.θ _ (M.Pσ σ (fun _ => M.hi) x) < M.hi
    rw [M.Pσ_const]
    exact (M.lo_lt_f_hi (M.c₁_lt x _ (σ.2 x)) (M.lt_c₂ x _ (σ.2 x))).2

theorem That_mem (σ : M.Policy) {v : X → ℝ} (hv : v ∈ Icc M.a M.b) : M.That σ v ∈ Icc M.a M.b :=
  have ha : M.a ∈ Icc M.a M.b := Set.left_mem_Icc.2 M.a_le_b
  have hb : M.b ∈ Icc M.a M.b := Set.right_mem_Icc.2 M.a_le_b
  ⟨fun x => ((M.exercise_5_1_9 σ).1 x).le.trans (M.That_le σ ha hv hv.1 x),
    fun x => (M.That_le σ hv hb hv.2 x).trans ((M.exercise_5_1_9 σ).2 x).le⟩

/-- The auxiliary ADP `(V̂, 𝕋̂_EZ)` on `V̂ = [v₁, v₂]`. -/
noncomputable def adpHat : ADP (Icc M.a M.b) M.Policy where
  T σ v := ⟨M.That σ v, M.That_mem σ v.2⟩
  mono σ v w h := M.That_le σ v.2 w.2 h
  nonempty := M.nonempty_policy

/-- **Exercise 5.1.10** (p. 158): (i) if `0 < θ ≤ 1`, `T̂_σ` is convex on `V̂`; (ii) if `θ < 0` or
`1 ≤ θ`, `T̂_σ` is concave on `V̂`. -/
theorem exercise_5_1_10 (σ : M.Policy) :
    (0 < M.θ → M.θ ≤ 1 → ConvexOn ℝ (Icc M.a M.b) (M.That σ)) ∧
      (M.θ < 0 ∨ 1 ≤ M.θ → ConcaveOn ℝ (Icc M.a M.b) (M.That σ)) := by
  refine ⟨fun h0 h1 => ⟨convex_Icc _ _, fun v hv w hw s t hs ht hst x => ?_⟩,
    fun hθ => ⟨convex_Icc _ _, fun v hv w hw s t hs ht hst x => ?_⟩⟩
  · change EZ.f M.β M.θ _ (M.Pσ σ (s • v + t • w) x) ≤ s * M.That σ v x + t * M.That σ w x
    rw [M.Pσ_combo]
    exact (EZ.convexOn_f M.β_nonneg M.β_lt_one (M.rα_pos x _) h0 h1).2 (M.Pσ_pos σ hv x)
      (M.Pσ_pos σ hw x) hs ht hst
  · change s * M.That σ v x + t * M.That σ w x ≤ EZ.f M.β M.θ _ (M.Pσ σ (s • v + t • w) x)
    rw [M.Pσ_combo]
    exact (EZ.concaveOn_f M.β_nonneg M.β_lt_one (M.rα_pos x _) hθ).2 (M.Pσ_pos σ hv x)
      (M.Pσ_pos σ hw x) hs ht hst

theorem adpHat_isFinite : M.adpHat.IsFinite := by
  have := M.finite_policy
  exact Set.finite_range _

/-- A policy maximizing (`max := true`) or minimizing `T̂_τ v (x)` over `Γ(x)` at every `x`. -/
theorem exists_extremal (v : Icc M.a M.b) (max : Bool) :
    ∃ σ : M.Policy, ∀ τ : M.Policy, if max then M.That τ v ≤ M.That σ v
      else M.That σ v ≤ M.That τ v := by
  let h : X → A → ℝ := fun x a' => EZ.f M.β M.θ (M.r x a' ^ M.α) (∑ x', v.1 x' * M.P x a' x')
  cases max with
  | true =>
    choose σ hσ hmax using fun x => Finset.exists_max_image (M.Γ x) (h x) (M.Γ_nonempty x)
    exact ⟨⟨σ, hσ⟩, fun τ x => hmax x (τ.1 x) (τ.2 x)⟩
  | false =>
    choose σ hσ hmin using fun x => Finset.exists_min_image (M.Γ x) (h x) (M.Γ_nonempty x)
    exact ⟨⟨σ, hσ⟩, fun τ x => hmin x (τ.1 x) (τ.2 x)⟩

theorem adpHat_regular : M.adpHat.Regular := fun v => by
  obtain ⟨σ, hσ⟩ := M.exists_extremal v true
  exact ⟨σ, fun τ => hσ τ⟩

theorem adpHat_minRegular : M.adpHat.MinRegular := fun v => by
  obtain ⟨σ, hσ⟩ := M.exists_extremal v false
  exact ⟨σ, fun τ => hσ τ⟩

/-- Every `T̂_σ` satisfies Du's conditions on `[v₁, v₂]` (proof of Lemma 5.1.11). -/
theorem duConditions (σ : M.Policy) :
    BanachLattice.DuConditions M.a M.b (BanachLattice.extendIcc (M.adpHat.T σ)) := by
  have heq : EqOn (M.That σ) (BanachLattice.extendIcc (M.adpHat.T σ)) (Icc M.a M.b) :=
    fun v hv => (BanachLattice.extendIcc_apply (M.adpHat.T σ) ⟨v, hv⟩).symm
  have ha : M.a ∈ Icc M.a M.b := Set.left_mem_Icc.2 M.a_le_b
  have hb : M.b ∈ Icc M.a M.b := Set.right_mem_Icc.2 M.a_le_b
  have hd : 0 < M.hi - M.lo := sub_pos.2 M.lo_lt_hi
  by_cases hθ : M.θ < 0 ∨ 1 ≤ M.θ
  · obtain ⟨ε, hε0, hε1, hε⟩ := exists_eps_mul_le (fun x => M.That σ M.a x - M.lo)
      (fun x => sub_pos.2 ((M.exercise_5_1_9 σ).1 x)) hd
    refine Or.inl ⟨((M.exercise_5_1_10 σ).2 hθ).congr heq, ε, hε0, hε1, ?_⟩
    rw [← heq ha]
    intro x
    change M.lo + ε * (M.hi - M.lo) ≤ M.That σ M.a x
    linarith [hε x]
  · have h0 : 0 < M.θ := lt_of_le_of_ne (not_lt.1 fun h => hθ (Or.inl h)) M.θ_ne.symm
    have h1 : M.θ ≤ 1 := (not_le.1 fun h => hθ (Or.inr h)).le
    obtain ⟨ε, hε0, hε1, hε⟩ := exists_eps_mul_le (fun x => M.hi - M.That σ M.b x)
      (fun x => sub_pos.2 ((M.exercise_5_1_9 σ).2 x)) hd
    refine Or.inr ⟨((M.exercise_5_1_10 σ).1 h0 h1).congr heq, ε, hε0, hε1, ?_⟩
    rw [← heq hb]
    intro x
    change M.That σ M.b x ≤ M.hi - ε * (M.hi - M.lo)
    linarith [hε x]

/-- Each `T̂_σ` is globally stable on `[v₁, v₂]` (Theorem 4.1.10), so `(V̂, 𝕋̂_EZ)` is order
stable. -/
theorem adpHat_isOrderStable : M.adpHat.IsOrderStable :=
  ADP.IsGloballyStable.isOrderStable fun σ =>
    BanachLattice.theorem_4_1_10_subtype M.a_le_b (M.adpHat.mono σ) (M.duConditions σ)

/-- **Lemma 5.1.11** (p. 158): (i) the fundamental max-optimality properties hold for
`(V̂, 𝕋̂_EZ)` and max-VFI, max-OPI and max-HPI all converge; (ii) the fundamental min-optimality
properties hold and min-VFI, min-OPI and min-HPI all converge. -/
theorem lemma_5_1_11 :
    (∃ hw : M.adpHat.WellPosed, M.adpHat.FundamentalOptimality hw ∧
      ∃ vstar, M.adpHat.IsValueFunction vstar ∧ M.adpHat.VFIConverges vstar ∧
        ∀ g, M.adpHat.IsSelector g → M.adpHat.OPIConverges g vstar ∧
          M.adpHat.HPIConverges hw g vstar) ∧
    (∃ hw : M.adpHat.WellPosed, M.adpHat.MinFundamentalOptimality hw ∧
      ∃ vstar, M.adpHat.IsMinValueFunction vstar ∧ M.adpHat.MinVFIConverges vstar ∧
        ∀ g, M.adpHat.IsMinSelector g → M.adpHat.MinOPIConverges g vstar ∧
          M.adpHat.MinHPIConverges hw g vstar) :=
  ⟨BanachLattice.theorem_4_1_11 M.a_le_b M.adpHat M.adpHat_regular M.duConditions
      (Or.inr (Or.inl M.adpHat_isFinite)),
    BanachLattice.theorem_4_1_11_min M.a_le_b M.adpHat M.adpHat_minRegular M.duConditions
      M.adpHat_isFinite⟩

/-! ### The Epstein–Zin ADP `(V, 𝕋_EZ)` -/

/-- `V = F⁻¹V̂ = {v ∈ (0, ∞)^X : v₁ ≤ v^ν ≤ v₂}` (5.12). -/
def V : Set (X → ℝ) := {v | (∀ x, 0 < v x) ∧ (fun x => v x ^ M.ν) ∈ Icc M.a M.b}

/-- `(L_σ v)(x) = (∑_{x'} v(x')^ν P(x, σ(x), x'))^{1/ν}`. -/
noncomputable def Lσ (σ : M.Policy) (v : X → ℝ) (x : X) : ℝ :=
  M.Pσ σ (fun x' => v x' ^ M.ν) x ^ M.ν⁻¹

/-- The Epstein–Zin policy operator (5.11), `T_σ v = {(1 − β)r_σ^α + β(L_σ v)^α}^{1/α}`. -/
noncomputable def Tσ (σ : M.Policy) (v : X → ℝ) : X → ℝ :=
  fun x => ((1 - M.β) * M.r x (σ.1 x) ^ M.α + M.β * M.Lσ σ v x ^ M.α) ^ M.α⁻¹

/-- **Exercise 5.1.11** (p. 159): `F ∘ T_σ = T̂_σ ∘ F` on `V`, with `Fv = v^ν`. -/
theorem exercise_5_1_11 (σ : M.Policy) {v : X → ℝ} (hv : v ∈ M.V) :
    (fun x => M.Tσ σ v x ^ M.ν) = M.That σ fun x => v x ^ M.ν := by
  funext x
  have hS := M.Pσ_pos σ hv.2 x
  have hL : M.Lσ σ v x ^ M.α = M.Pσ σ (fun x' => v x' ^ M.ν) x ^ M.θ⁻¹ := by
    rw [Lσ, ← Real.rpow_mul hS.le, θ, inv_div, div_eq_inv_mul]
  have hA : 0 < (1 - M.β) * M.r x (σ.1 x) ^ M.α + M.β * M.Lσ σ v x ^ M.α :=
    add_pos_of_pos_of_nonneg (mul_pos (sub_pos.2 M.β_lt_one) (M.rα_pos x _))
      (mul_nonneg M.β_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hS.le _) _))
  rw [Tσ, ← Real.rpow_mul hA.le, hL]
  change _ = ((1 - M.β) * M.r x (σ.1 x) ^ M.α + M.β * _ ^ M.θ⁻¹) ^ M.θ
  rw [θ, div_eq_inv_mul]

theorem Tσ_mem (σ : M.Policy) {v : X → ℝ} (hv : v ∈ M.V) : M.Tσ σ v ∈ M.V := by
  refine ⟨fun x => ?_, ?_⟩
  · have hS := M.Pσ_pos σ hv.2 x
    exact Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg (mul_pos (sub_pos.2 M.β_lt_one)
      (M.rα_pos x _)) (mul_nonneg M.β_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hS.le _) _))) _
  · rw [M.exercise_5_1_11 σ hv]
    exact M.That_mem σ hv.2

/-- `F v = v^ν` as a map `V → V̂`. -/
noncomputable def Φ (v : M.V) : Icc M.a M.b := ⟨fun x => v.1 x ^ M.ν, v.2.2⟩

/-- The inverse `v̂ ↦ v̂^{1/ν}`. -/
noncomputable def Ψ (w : Icc M.a M.b) : M.V :=
  ⟨fun x => w.1 x ^ M.ν⁻¹, fun x => Real.rpow_pos_of_pos (M.lo_pos.trans_le (w.2.1 x)) _, by
    have : (fun x => (w.1 x ^ M.ν⁻¹) ^ M.ν) = w.1 := funext fun x =>
      Real.rpow_inv_rpow (M.lo_pos.trans_le (w.2.1 x)).le M.ν_ne
    rw [this]
    exact w.2⟩

theorem Φ_Ψ (w : Icc M.a M.b) : M.Φ (M.Ψ w) = w :=
  Subtype.ext (funext fun x => Real.rpow_inv_rpow (M.lo_pos.trans_le (w.2.1 x)).le M.ν_ne)

theorem Ψ_Φ (v : M.V) : M.Ψ (M.Φ v) = v :=
  Subtype.ext (funext fun x => Real.rpow_rpow_inv (v.2.1 x).le M.ν_ne)

/-- For `ν > 0`, `F` is an order isomorphism `V → V̂`. -/
noncomputable def isoPos (hν : 0 < M.ν) : M.V ≃o Icc M.a M.b where
  toFun := M.Φ
  invFun := M.Ψ
  left_inv := M.Ψ_Φ
  right_inv := M.Φ_Ψ
  map_rel_iff' {v w} := by
    change (∀ x, v.1 x ^ M.ν ≤ w.1 x ^ M.ν) ↔ ∀ x, v.1 x ≤ w.1 x
    exact forall_congr' fun x => Real.rpow_le_rpow_iff (v.2.1 x).le (w.2.1 x).le hν

/-- For `ν < 0`, `F` is an order anti-isomorphism `V → V̂`. -/
noncomputable def isoNeg (hν : M.ν < 0) : M.V ≃o (Icc M.a M.b)ᵒᵈ where
  toFun v := OrderDual.toDual (M.Φ v)
  invFun w := M.Ψ (OrderDual.ofDual w)
  left_inv := M.Ψ_Φ
  right_inv w := congrArg OrderDual.toDual (M.Φ_Ψ (OrderDual.ofDual w))
  map_rel_iff' {v w} := by
    change (∀ x, w.1 x ^ M.ν ≤ v.1 x ^ M.ν) ↔ ∀ x, v.1 x ≤ w.1 x
    exact forall_congr' fun x => Real.rpow_le_rpow_iff_of_neg (w.2.1 x) (v.2.1 x) hν

theorem Φ_T (σ : M.Policy) (v : M.V) :
    M.Φ ⟨M.Tσ σ v.1, M.Tσ_mem σ v.2⟩ = M.adpHat.T σ (M.Φ v) :=
  Subtype.ext (M.exercise_5_1_11 σ v.2)

/-- The Epstein–Zin ADP `(V, 𝕋_EZ)`. -/
noncomputable def adp : ADP M.V M.Policy where
  T σ v := ⟨M.Tσ σ v.1, M.Tσ_mem σ v.2⟩
  mono σ v w h := by
    rcases lt_or_gt_of_ne M.ν_ne with hneg | hpos
    · refine (M.isoNeg hneg).le_iff_le.1 ?_
      change M.Φ ⟨M.Tσ σ w.1, M.Tσ_mem σ w.2⟩ ≤ M.Φ ⟨M.Tσ σ v.1, M.Tσ_mem σ v.2⟩
      rw [M.Φ_T, M.Φ_T]
      exact M.adpHat.mono σ ((M.isoNeg hneg).le_iff_le.2 h)
    · refine (M.isoPos hpos).le_iff_le.1 ?_
      change M.Φ ⟨M.Tσ σ v.1, M.Tσ_mem σ v.2⟩ ≤ M.Φ ⟨M.Tσ σ w.1, M.Tσ_mem σ w.2⟩
      rw [M.Φ_T, M.Φ_T]
      exact M.adpHat.mono σ ((M.isoPos hpos).le_iff_le.2 h)
  nonempty := M.nonempty_policy

/-- **Lemma 5.1.12 (i)** (p. 159): if `ν > 0`, `(V, 𝕋_EZ)` and `(V̂, 𝕋̂_EZ)` are isomorphic. -/
theorem lemma_5_1_12_i (hν : 0 < M.ν) : M.adp.IsIsomorphic M.adpHat (M.isoPos hν) :=
  fun σ v => M.Φ_T σ v

/-- **Lemma 5.1.12 (ii)**: if `ν < 0`, `(V, 𝕋_EZ)` and `(V̂, 𝕋̂_EZ)` are anti-isomorphic. -/
theorem lemma_5_1_12_ii (hν : M.ν < 0) : M.adp.IsAntiIsomorphic M.adpHat (M.isoNeg hν) :=
  fun σ v => M.Φ_T σ v

/-- `(V, 𝕋_EZ)` is order stable. -/
theorem adp_isOrderStable : M.adp.IsOrderStable := by
  rcases lt_or_gt_of_ne M.ν_ne with hneg | hpos
  · exact (ADP.theorem_5_1_8 (M.lemma_5_1_12_ii hneg)).2.2.2.1.2 M.adpHat_isOrderStable
  · exact (M.lemma_5_1_12_i hpos).orderStable_iff.2 M.adpHat_isOrderStable

/-- **Proposition 5.1.13** (p. 159): the fundamental max-optimality properties hold for
`(V, 𝕋_EZ)`, and max-VFI, max-OPI and max-HPI all converge. -/
theorem proposition_5_1_13 :
    ∃ hw : M.adp.WellPosed, M.adp.FundamentalOptimality hw ∧
      ∃ vstar, M.adp.IsValueFunction vstar ∧ M.adp.VFIConverges vstar ∧
        ∀ g, M.adp.IsSelector g → M.adp.OPIConverges g vstar ∧ M.adp.HPIConverges hw g vstar := by
  rcases lt_or_gt_of_ne M.ν_ne with hneg | hpos
  · have h := M.lemma_5_1_12_ii hneg
    obtain ⟨hw', hFO', w, hw₀, hvfi, hconv⟩ := M.lemma_5_1_11.2
    have h8 := ADP.theorem_5_1_8 h
    have hr : M.adp.Regular := h8.2.1.2 M.adpHat_minRegular
    have hw : M.adp.WellPosed := h8.2.2.1.2 hw'
    set vstar := (M.isoNeg hneg).symm (OrderDual.toDual w)
    have hF : OrderDual.ofDual (M.isoNeg hneg vstar) = w := by simp [vstar]
    have h10 := ADP.theorem_5_1_10 h hr hw hw' vstar
    rw [hF] at h10
    refine ⟨hw, ((ADP.theorem_5_1_9 h hr hw hw').2.2).2 hFO', vstar, ?_, h10.2.2.1.2 hvfi,
      fun g hg => ⟨h10.2.2.2.1.2 (fun g' hg' => (hconv g' hg').1) g hg,
        h10.2.2.2.2.2 (fun g' hg' => (hconv g' hg').2) g hg⟩⟩
    refine (h.iso.isValueFunction_iff vstar).2 ?_
    have hv : M.isoNeg hneg vstar = OrderDual.toDual w := by simp [vstar]
    rw [hv]
    exact (M.adpHat.isMinValueFunction_iff w).1 hw₀
  · have h := M.lemma_5_1_12_i hpos
    obtain ⟨hw', hFO', w, hw₀, hvfi, hconv⟩ := M.lemma_5_1_11.1
    have hr : M.adp.Regular := h.regular_iff.2 M.adpHat_regular
    have hw : M.adp.WellPosed := h.wellPosed_iff.2 hw'
    set vstar := (M.isoPos hpos).symm w
    have hF : M.isoPos hpos vstar = w := by simp [vstar]
    have h7 := ADP.theorem_5_1_7 h hr hw hw' vstar
    rw [hF] at h7
    refine ⟨hw, (h.fundamentalOptimality_iff hw hw').2 hFO', vstar, ?_, h7.2.2.1.2 hvfi,
      fun g hg => ⟨h7.2.2.2.1.2 (fun g' hg' => (hconv g' hg').1) g hg,
        h7.2.2.2.2.2 (fun g' hg' => (hconv g' hg').2) g hg⟩⟩
    rw [h.isValueFunction_iff, hF]
    exact hw₀

end EZModel

end SargentStachurski.ADPTransformations
