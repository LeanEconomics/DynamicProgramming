/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ADPsOnPospaces.ContractingDP
import ADPsOnPospaces.NeumannSeries
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Optimal savings

Sargent and Stachurski, *Dynamic Programming*, Volume 2, §1.3.1–§1.3.2 (pp. 36–43).

Wealth `w ∈ ℝ₊` evolves as `W_{t+1} = R(W_t − C_t) + Y_{t+1}` with iid income `Y ∼ φ`, and
utility `u` is continuous and bounded (Assumption 1.3.1; the density of `φ` is not needed
here). A feasible policy is a Borel `σ : ℝ₊ → ℝ₊` with `σ(w) ≤ w`.

* **Exercise 1.3.1** and **Lemma 1.3.1**: each policy operator
  `(T_σ v)(w) = u(σ(w)) + β ∫ v(R(w − σ(w)) + y) φ(dy)` (1.42) maps `bℝ₊` into itself and is
  globally stable, with fixed point `v_σ = (I − βP_σ)⁻¹r_σ = ∑ₜ (βP_σ)ᵗr_σ` (1.44); lifetime
  values are limits of finite-horizon values (1.47).
* (1.48): `|v_σ| ≤ M/(1 − β)` when `|u| ≤ M`, so `v* = sup_σ v_σ` is well defined.
* **Exercise 1.3.2**: the Bellman operator (1.51) is a `β`-contraction.
* §2.3.2: a policy is greedy in the dynamic-program sense iff it is `v`-greedy in the sense
  of (1.49) (a policy can be changed at a single wealth level).
* §1.3.2.2, (i)–(iii): given the existence of greedy policies (Lemma 1.3.2 (i), which rests on
  the density of `φ` and is proved in Chapter 6), an optimal policy exists, `v*` is the unique
  solution of the Bellman equation (1.50) in `bℝ₊`, and a policy is optimal iff it is
  `v*`-greedy.
-/

open MeasureTheory Filter Topology Set Function

open scoped NNReal

namespace SargentStachurski.ADPsOnPospaces

/-- The optimal savings problem of §1.3 (with bounded continuous utility). -/
structure OptimalSavings where
  /-- the utility function -/
  u : ℝ≥0 → ℝ
  u_cont : Continuous u
  u_bdd : IsBdd u
  /-- the distribution of labor income -/
  φ : Measure ℝ≥0
  φ_prob : IsProbabilityMeasure φ
  /-- the discount factor -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the gross return on assets -/
  R : ℝ≥0

/-- Feasible policies (§1.3.1.1): Borel `σ` with `0 ≤ σ(w) ≤ w`. -/
def SavingsPolicy : Type := {σ : ℝ≥0 → ℝ≥0 // Measurable σ ∧ ∀ w, σ w ≤ w}

namespace OptimalSavings

variable (S : OptimalSavings)

/-- The expected continuation value of saving `w − c`: `∫ v(R(w − c) + y) φ(dy)`. -/
noncomputable def cont (v : ℝ≥0 → ℝ) (w c : ℝ≥0) : ℝ := ∫ y, v (S.R * (w - c) + y) ∂S.φ

/-- The Markov operator `(P_σ v)(w) = ∫ v(R(w − σ(w)) + y) φ(dy)` (proof of Lemma 1.3.1). -/
noncomputable def Pσ (σ : ℝ≥0 → ℝ≥0) (v : ℝ≥0 → ℝ) (w : ℝ≥0) : ℝ := S.cont v w (σ w)

/-- `r_σ = u ∘ σ`. -/
def rσ (σ : ℝ≥0 → ℝ≥0) : ℝ≥0 → ℝ := fun w => S.u (σ w)

/-- The policy operator (1.42): `(T_σ v)(w) = u(σ(w)) + β ∫ v(R(w − σ(w)) + y) φ(dy)`. -/
noncomputable def Tσ (σ : ℝ≥0 → ℝ≥0) : (ℝ≥0 → ℝ) → ℝ≥0 → ℝ := affineOp (S.rσ σ) S.β (S.Pσ σ)

theorem integrable_comp {v : ℝ≥0 → ℝ} (hv : v ∈ bX ℝ≥0) (a : ℝ≥0) :
    Integrable (fun y => v (a + y)) S.φ := by
  have := S.φ_prob
  obtain ⟨M, hM⟩ := hv.2
  exact Integrable.of_bound (hv.1.comp (measurable_const.add measurable_id)).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM _)

theorem abs_cont_le {v : ℝ≥0 → ℝ} {M : ℝ} (hM : ∀ w, |v w| ≤ M) (w c : ℝ≥0) :
    |S.cont v w c| ≤ M := by
  have := S.φ_prob
  have := norm_integral_le_of_norm_le_const (μ := S.φ) (f := fun y => v (S.R * (w - c) + y))
    (C := M) (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM _)
  simpa [cont] using this

/-- `P_σ` is a Markov operator on `bℝ₊`. -/
theorem isMarkovLike_Pσ {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) : IsMarkovLike (S.Pσ σ) := by
  have := S.φ_prob
  refine ⟨fun v hv => ?_, fun v hv w hw => ?_, fun a v _ => ?_, fun v hv w hw h => ?_,
    fun v hv M hM x => S.abs_cont_le hM _ _⟩
  · obtain ⟨M, hM⟩ := hv.2
    have hf : StronglyMeasurable fun p : ℝ≥0 × ℝ≥0 => v (S.R * (p.1 - σ p.1) + p.2) :=
      (hv.1.comp ((measurable_const.mul (measurable_fst.sub (hσ.comp measurable_fst))).add
        measurable_snd)).stronglyMeasurable
    exact ⟨hf.integral_prod_right'.measurable, M, fun w => S.abs_cont_le hM _ _⟩
  · funext x
    exact integral_add (S.integrable_comp hv _) (S.integrable_comp hw _)
  · funext x
    simp only [Pσ, cont, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul a _
  · intro x
    exact integral_mono (S.integrable_comp hv _) (S.integrable_comp hw _) fun y => h _

theorem rσ_mem {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) : S.rσ σ ∈ bX ℝ≥0 := by
  obtain ⟨M, hM⟩ := S.u_bdd
  exact ⟨S.u_cont.measurable.comp hσ, M, fun w => hM _⟩

/-- **Exercise 1.3.1** (p. 38): `T_σ` maps `bℝ₊` into itself. -/
theorem Tσ_mapsTo {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) : MapsTo (S.Tσ σ) (bX ℝ≥0) (bX ℝ≥0) :=
  affineOp_mapsTo (S.isMarkovLike_Pσ hσ) (S.rσ_mem hσ) S.β_nonneg

/-- **Lemma 1.3.1** (p. 38) and (1.47): each `T_σ` is globally stable on `bℝ₊`: it has a unique
fixed point `v_σ`, and `T_σᵏ v → v_σ` from every terminal value `v ∈ bℝ₊`. -/
theorem Tσ_globallyStable {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) :
    ∃ u ∈ bX ℝ≥0, S.Tσ σ u = u ∧ (∀ w ∈ bX ℝ≥0, S.Tσ σ w = w → w = u) ∧
      ∀ v ∈ bX ℝ≥0, TendstoUniformly (fun n => (S.Tσ σ)^[n] v) u atTop :=
  affineOp_globallyStable (S.isMarkovLike_Pσ hσ) (S.rσ_mem hσ) S.β_nonneg S.β_lt_one

/-- **Lemma 1.3.1**, (1.44): the fixed point of `T_σ` is `v_σ = ∑ₜ (βP_σ)ᵗr_σ`. -/
theorem vσ_hasSum {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) {v : ℝ≥0 → ℝ} (hv : v ∈ bX ℝ≥0)
    (hfix : S.Tσ σ v = v) (w : ℝ≥0) :
    HasSum (fun t => S.β ^ t * (S.Pσ σ)^[t] (S.rσ σ) w) (v w) :=
  affineOp_hasSum (S.isMarkovLike_Pσ hσ) (S.rσ_mem hσ) S.β_nonneg S.β_lt_one hv hfix w

/-- (1.48) (p. 40): if `|u| ≤ M` then `|v_σ| ≤ M/(1 − β)`; so `v* = sup_σ v_σ` is well defined. -/
theorem abs_fixedPoint_le {σ : ℝ≥0 → ℝ≥0} (hσ : Measurable σ) {M : ℝ}
    (hM : ∀ w, |S.u w| ≤ M) {v : ℝ≥0 → ℝ} (hv : v ∈ bX ℝ≥0) (hfix : S.Tσ σ v = v)
    (w : ℝ≥0) : |v w| ≤ M / (1 - S.β) := by
  have hL := S.isMarkovLike_Pσ hσ
  have h1β : 0 < 1 - S.β := sub_pos.2 S.β_lt_one
  obtain ⟨u, -, -, huniq, hlim⟩ := S.Tσ_globallyStable hσ
  rw [huniq v hv hfix]
  -- the iterates from `0` stay within `M/(1 − β)`
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK : M + S.β * (M / (1 - S.β)) = M / (1 - S.β) := by
    field_simp
    ring
  have hit : ∀ n x, |(S.Tσ σ)^[n] (fun _ => 0) x| ≤ M / (1 - S.β) := by
    intro n
    induction n with
    | zero => intro x; simpa using div_nonneg hM0 h1β.le
    | succ n ih =>
      intro x
      rw [iterate_succ_apply']
      have hmem : (S.Tσ σ)^[n] (fun _ => 0) ∈ bX ℝ≥0 := (S.Tσ_mapsTo hσ).iterate n (const_mem_bX 0)
      calc |S.rσ σ x + S.β * S.Pσ σ ((S.Tσ σ)^[n] fun _ => 0) x|
          ≤ |S.rσ σ x| + S.β * |S.Pσ σ ((S.Tσ σ)^[n] fun _ => 0) x| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_nonneg S.β_nonneg]
        _ ≤ M + S.β * (M / (1 - S.β)) :=
            add_le_add (hM _) (mul_le_mul_of_nonneg_left (hL.abs_le _ hmem _ ih x) S.β_nonneg)
        _ = M / (1 - S.β) := hK
  exact le_of_tendsto' ((hlim _ (const_mem_bX 0)).tendsto_at w).abs fun n => hit n w

/-! ### The Bellman operator -/

/-- The objective in (1.49)–(1.51): `u(c) + β ∫ v(R(w − c) + y) φ(dy)`. -/
noncomputable def objective (v : ℝ≥0 → ℝ) (w c : ℝ≥0) : ℝ := S.u c + S.β * S.cont v w c

/-- The Bellman operator (1.51): `(Tv)(w) = max_{0 ≤ c ≤ w} {u(c) + β ∫ v(R(w − c) + y) φ(dy)}`. -/
noncomputable def bellmanOp (v : ℝ≥0 → ℝ) (w : ℝ≥0) : ℝ :=
  ⨆ c : {c : ℝ≥0 // c ≤ w}, S.objective v w c

theorem bddAbove_objective {v : ℝ≥0 → ℝ} (hv : IsBdd v) (w : ℝ≥0) :
    BddAbove (range fun c : {c : ℝ≥0 // c ≤ w} => S.objective v w c) := by
  obtain ⟨M, hM⟩ := S.u_bdd
  obtain ⟨N, hN⟩ := hv
  refine ⟨M + S.β * N, ?_⟩
  rintro _ ⟨c, rfl⟩
  refine add_le_add (le_of_abs_le (hM _)) (mul_le_mul_of_nonneg_left ?_ S.β_nonneg)
  exact le_of_abs_le (S.abs_cont_le hN _ _)

/-- **Exercise 1.3.2** (p. 42): the Bellman operator is a `β`-contraction on `bℝ₊`. -/
theorem bellmanOp_contraction : IsSupContraction (bX ℝ≥0) S.bellmanOp S.β := by
  intro v hv v' hv' c h w
  have : Nonempty {c : ℝ≥0 // c ≤ w} := ⟨⟨0, bot_le⟩⟩
  refine abs_ciSup_sub_ciSup_le (S.bddAbove_objective hv.2 w) (S.bddAbove_objective hv'.2 w)
    fun d => ?_
  have hvv' : v - v' ∈ bX ℝ≥0 := ⟨hv.1.sub hv'.1, hv.2.sub hv'.2⟩
  have hsub : S.cont v w d - S.cont v' w d = S.cont (v - v') w d := by
    have := S.φ_prob
    simp only [cont, Pi.sub_apply]
    exact (integral_sub (S.integrable_comp hv _) (S.integrable_comp hv' _)).symm
  simp only [objective, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_of_nonneg S.β_nonneg,
    hsub]
  exact mul_le_mul_of_nonneg_left (S.abs_cont_le h _ _) S.β_nonneg

/-! ### Greedy policies and optimality -/

/-- `σ` is `v`-greedy (1.49): `σ(w)` maximizes `u(c) + β ∫ v(R(w − c) + y) φ(dy)` over
`0 ≤ c ≤ w`, for every `w`. -/
def IsGreedy (v : ℝ≥0 → ℝ) (σ : SavingsPolicy) : Prop :=
  ∀ w, ∀ c ≤ w, S.objective v w c ≤ S.objective v w (σ.1 w)

/-- The optimal savings problem as a contracting dynamic program, given that greedy policies
exist (Lemma 1.3.2 (i)). -/
noncomputable def toDP (hgreedy : ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ) :
    ContractingDP ℝ≥0 SavingsPolicy where
  V := bX ℝ≥0
  T σ := S.Tσ σ.1
  β := S.β
  β_nonneg := S.β_nonneg
  β_lt_one := S.β_lt_one
  nonempty := ⟨_, const_mem_bX 0⟩
  bdd _ h := h.2
  closed := isUniformlyClosed_bX
  mapsTo σ := S.Tσ_mapsTo σ.2.1
  mono σ _ hv _ hw h := affineOp_mono (S.isMarkovLike_Pσ σ.2.1) S.β_nonneg hv hw h
  contraction σ := affineOp_contraction (S.isMarkovLike_Pσ σ.2.1) S.β_nonneg
  exists_greedy v hv := by
    obtain ⟨σ, hσ⟩ := hgreedy v hv
    exact ⟨σ, fun τ w => hσ w _ (τ.2.2 w)⟩

variable {S} (hgreedy : ∀ v ∈ bX ℝ≥0, ∃ σ, S.IsGreedy v σ)

/-- §2.3.2 (p. 81): `σ` is greedy for the dynamic program (`T_τ v ≤ T_σ v` for all feasible `τ`)
iff it is `v`-greedy in the sense of (1.49). -/
theorem isGreedy_iff (v : ℝ≥0 → ℝ) (σ : SavingsPolicy) :
    S.IsGreedy v σ ↔ (S.toDP hgreedy).IsGreedy v σ := by
  constructor
  · exact fun h τ w => h w _ (τ.2.2 w)
  · intro h w c hc
    classical
    let τ : SavingsPolicy := ⟨fun x => if x = w then c else σ.1 x,
      Measurable.ite (measurableSet_singleton w) measurable_const σ.2.1, fun x => by
        by_cases hx : x = w
        · simp only [hx, ↓reduceIte]; exact hc
        · simp only [hx, ↓reduceIte]; exact σ.2.2 x⟩
    have := h τ w
    change S.Tσ (fun x => if x = w then c else σ.1 x) v w ≤ S.Tσ σ.1 v w at this
    simpa [Tσ, affineOp, rσ, Pσ, objective] using this

/-- (1.51): the Bellman operator of the dynamic program is
`(Tv)(w) = max_{0 ≤ c ≤ w} {u(c) + β ∫ v(R(w − c) + y) φ(dy)}`. -/
theorem bellman_eq {v : ℝ≥0 → ℝ} (hv : v ∈ bX ℝ≥0) (w : ℝ≥0) :
    (S.toDP hgreedy).bellman v w = S.bellmanOp v w := by
  have hg := (isGreedy_iff hgreedy v _).2 ((S.toDP hgreedy).isGreedy_greedy hv)
  have : Nonempty {c : ℝ≥0 // c ≤ w} := ⟨⟨0, bot_le⟩⟩
  refine le_antisymm ?_ (ciSup_le fun c => hg w c c.2)
  exact le_ciSup (S.bddAbove_objective hv.2 w) ⟨((S.toDP hgreedy).greedy v).1 w,
    ((S.toDP hgreedy).greedy v).2.2 w⟩

/-- **§1.3.2.2** (p. 42), given greedy policies (Lemma 1.3.2 (i)): (i) an optimal policy
exists, (ii) `v*` is the unique solution of the Bellman equation (1.50) in `bℝ₊`, and (iii) a
policy is optimal iff it is `v*`-greedy. -/
theorem dp_results :
    (∃ σ, (S.toDP hgreedy).IsOptimal σ) ∧
      (S.toDP hgreedy).vstar ∈ bX ℝ≥0 ∧
      (∀ w, (S.toDP hgreedy).vstar w = S.bellmanOp (S.toDP hgreedy).vstar w) ∧
      (∀ v ∈ bX ℝ≥0, (∀ w, v w = S.bellmanOp v w) → v = (S.toDP hgreedy).vstar) ∧
      ∀ σ, (S.toDP hgreedy).IsOptimal σ ↔ S.IsGreedy (S.toDP hgreedy).vstar σ := by
  obtain ⟨-, -, hfix, hopt, hex, -⟩ := (S.toDP hgreedy).optimality
  have hmem := (S.toDP hgreedy).vstar_mem
  refine ⟨hex, hmem, fun w => ?_, fun v hv h => (hfix v hv).1 (funext fun w => ?_),
    fun σ => (hopt σ).trans (isGreedy_iff hgreedy _ σ).symm⟩
  · rw [← bellman_eq hgreedy hmem, (S.toDP hgreedy).bellman_vstar]
  · rw [bellman_eq hgreedy hv]; exact (h w).symm

end OptimalSavings

end SargentStachurski.ADPsOnPospaces
