/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManyConsumersPareto

/-!
# The operator `T` of §16.7

SLP §16.7, pp. 498–499. Functions `f : ℝᵖ → ℝᴵ → ℝ` are used only on `ℝᵖ₊ × Δᴵ`.

* `mcUpper f κ′` is `𝒰_f(κ′) = {z′ ∈ ℝᴵ₊ : θ′ · z′ ≤ f(κ′, θ′) ∀θ′ ∈ Δᴵ}`; `mcConstraint Φ f κ` is
  the constraint set of (4); `mcObjective W θ` its objective; `mcOperator W Φ f` is `T` (p. 498).
* `MCInF f`: `f` is in the space `F` (bounded, continuous, nonnegative). `mcSupportType f`: each
  `f(κ, ·)` is the support function on `Δᴵ` of `𝒰_f(κ)`. `MCAdmissible f`: bounded, nonnegative,
  of support-function type.
* Basic properties: `mcOperator_nonneg`, `mcOperator_bdd`, `mcOperator_mono` (Blackwell's
  monotonicity), `mcOperator_supportType` (every `Tf` is of support-function type),
  `mcOperator_admissible`.
* **Exercise 16.7d** (p. 499): `ex_16_7d_compact` (the constraint set is compact for `f ∈ F`),
  `mcObjective_continuousOn`, `ex_16_7d_exists_max` (the supremum `Tf(κ, θ)` is attained),
  `ex_16_7d_convex` (convexity for `f` concave in `κ′`), `mcObjective_concave`.
* **Exercise 16.7f** (p. 499): `mcUpper_isCompact`, `convex_mcUpper`; `ex_16_7f_hint` (`𝒰ᵃ = B`
  for `f` of support-function type); `mcOperator_discount` (`T(f + a) ≤ Tf + βa`); `ex_16_7f`
  (contraction with modulus `β = maxᵢ βᵢ` on admissible functions); `mcSupportType_of_tendsto`
  (admissible functions are closed under bounded pointwise limits); `ex_16_7f_exists_fixed`,
  `ex_16_7f_unique` (a unique admissible solution of (4), the limit of `Tⁿ0`).
* **(4) and the Principle of Optimality** (pp. 498–499): `mcSupport_admissible`; `mc_eq4`
  (`v = Tv` when every `U(κ′)` is closed); `mc_support_unique_fixed` (then the support function
  (2) is the unique admissible solution of (4): the "Try it!" question of p. 499).
* **Exercise 16.7g** (p. 499): `mcSupport_concave` (`v(·, θ)` concave),
  `ex_16_7g_convex_of_concave`,
  `ex_16_7g` (the policy correspondence of (4) for `f = v` is convex-valued).

**Corrections.**
* (d): the constraint set is compact but not convex for general `f ∈ F`
  (`ex_16_7d_counterexample`); it is convex when every `f(·, θ′)` is concave on `ℝᵖ₊`.
* (e): `T` does not map `F` into `F` (`ex_16_7e_counterexample`): the constraint correspondence is
  not lower hemicontinuous and `Tf` can jump. (The transcription's NOTE only says lower
  hemicontinuity is not addressed.) Proved instead: `Tf` is bounded, nonnegative and of
  support-function type for every bounded nonnegative `f`. The corrected statement, `T` maps
  `F_s = F ∩ {support-function type}` into itself, is `ex_16_7e` in `ManyConsumersBerge`.
* (f): the hint's `𝒰ᵃ = B` is false for general `f ∈ F` (`ex_16_7f_hint_counterexample`), and so is
  the conclusion: on `F`, `T` is not a contraction with modulus `β`, nor with any modulus `< 1`
  (`ex_16_7f_counterexample`). It is a `β`-contraction on admissible functions (`ex_16_7f`), which
  contain `T(F)` and are closed under bounded pointwise limits; the fixed point is found there
  (continuity dropped), and it is the support function (2) when every `U(κ)` is closed.
* (g): convex-valuedness needs `f` concave in `κ′`; it holds for `f = v`. Upper hemicontinuity of
  the policy correspondence is `ex_16_7g_uhc` and `ex_16_7g_support` in
  `ManyConsumersBerge`. The policy
  correspondence need not be single-valued (`W` is concave, not strictly).
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set

variable {l p : ℕ} {Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))} {ι : Type*} [Fintype ι]

/-! ### The constraint set and the operator `T` (p. 498) -/

/-- The set `𝒰_f(κ′) = {z′ ∈ ℝᴵ₊ : f(κ′, θ′) ≥ θ′ · z′ ∀θ′ ∈ Δᴵ}` (the constraint on `z′` in (4);
`𝒰` of the hint to Exercise 16.7f). -/
def mcUpper (f : (Fin p → ℝ) → (ι → ℝ) → ℝ) (κ' : Fin p → ℝ) : Set (ι → ℝ) :=
  {z | 0 ≤ z ∧ ∀ θ ∈ mcSimplex ι, ∑ i, θ i * z i ≤ f κ' θ}

/-- The constraint set of (4) at `κ`: triples `(γ, z′, κ′)` with `γᵢ ≥ 0`, `(Σᵢ γᵢ, κ′) ∈ Φ(κ)` and
`z′ ∈ 𝒰_f(κ′)`. -/
def mcConstraint (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ)))
    (f : (Fin p → ℝ) → (ι → ℝ) → ℝ) (κ : Fin p → ℝ) :
    Set ((ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)) :=
  {q | (∀ i, 0 ≤ q.1 i) ∧ (∑ i, q.1 i, q.2.2) ∈ Φ κ ∧ q.2.1 ∈ mcUpper f q.2.2}

/-- The objective of (4): `Σᵢ θᵢ Wᵢ(γᵢ, z′ᵢ)`. -/
def mcObjective (W : ι → (Fin l → ℝ) → ℝ → ℝ) (θ : ι → ℝ)
    (q : (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)) : ℝ :=
  ∑ i, θ i * W i (q.1 i) (q.2.1 i)

/-- The **operator `T`** of (4), p. 498: `(Tf)(κ, θ) = sup Σᵢ θᵢ Wᵢ(γᵢ, z′ᵢ)` over the constraint
set. -/
noncomputable def mcOperator (W : ι → (Fin l → ℝ) → ℝ → ℝ)
    (Φ : (Fin p → ℝ) → Set ((Fin l → ℝ) × (Fin p → ℝ))) (f : (Fin p → ℝ) → (ι → ℝ) → ℝ)
    (κ : Fin p → ℝ) (θ : ι → ℝ) : ℝ :=
  sSup (mcObjective W θ '' mcConstraint Φ f κ)

/-- The space `F` of p. 498: `f : ℝᵖ₊ × Δᴵ → ℝ₊` bounded and continuous. -/
structure MCInF (f : (Fin p → ℝ) → (ι → ℝ) → ℝ) : Prop where
  cont : ContinuousOn (fun x : (Fin p → ℝ) × (ι → ℝ) => f x.1 x.2) (Ici 0 ×ˢ mcSimplex ι)
  bdd : ∃ M, ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, f κ θ ≤ M
  nonneg : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, 0 ≤ f κ θ

/-- `f` is of **support-function type**: each `f(κ, ·)` is the support function on `Δᴵ` of its
own set `𝒰_f(κ)`, i.e. `f(κ, θ) = sup_{z ∈ 𝒰_f(κ)} θ · z` (`≥` always holds). -/
def mcSupportType (f : (Fin p → ℝ) → (ι → ℝ) → ℝ) : Prop :=
  ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, ∀ ε > 0, ∃ z ∈ mcUpper f κ, f κ θ - ε < ∑ i, θ i * z i

/-- The **admissible** functions: bounded, nonnegative and of support-function type (continuity is
dropped; see the NOTE to Exercise 16.7e). The corrected contraction argument runs here. -/
structure MCAdmissible (f : (Fin p → ℝ) → (ι → ℝ) → ℝ) : Prop where
  bdd : ∃ M, ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, f κ θ ≤ M
  nonneg : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, 0 ≤ f κ θ
  support : mcSupportType f

/-- The unit vector `eᵢ` lies in `Δᴵ`. -/
theorem mc_single_mem_simplex [DecidableEq ι] (i : ι) : Pi.single i 1 ∈ mcSimplex ι := by
  refine ⟨fun j => ?_, by simp⟩
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [h]

/-- `eᵢ · z = zᵢ`. -/
theorem mc_single_dot [DecidableEq ι] (i : ι) (z : ι → ℝ) :
    ∑ j, (Pi.single i 1 : ι → ℝ) j * z j = z i := by
  simp [Pi.single_apply]

/-- `θ · (z + a𝟙) = θ · z + a` on `Δᴵ`. -/
theorem mc_dot_add_const {θ : ι → ℝ} (hθ : θ ∈ mcSimplex ι) (z : ι → ℝ) (a : ℝ) :
    ∑ i, θ i * (z i + a) = ∑ i, θ i * z i + a := by
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hθ.2, one_mul]

/-- Points of `𝒰_f(κ′)` satisfy `zᵢ ≤ f(κ′, eᵢ)`. -/
theorem mcUpper_le [DecidableEq ι] {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} {κ' : Fin p → ℝ}
    {z : ι → ℝ} (hz : z ∈ mcUpper f κ') (i : ι) : z i ≤ f κ' (Pi.single i 1) := by
  have := hz.2 _ (mc_single_mem_simplex i)
  rwa [mc_single_dot] at this

/-- `0 ∈ 𝒰_f(κ′)` when `f(κ′, ·) ≥ 0`. -/
theorem zero_mem_mcUpper {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} {κ' : Fin p → ℝ}
    (hf : ∀ θ ∈ mcSimplex ι, 0 ≤ f κ' θ) : (0 : ι → ℝ) ∈ mcUpper f κ' :=
  ⟨le_rfl, fun θ hθ => by simpa using hf θ hθ⟩

/-- The constraint set is nonempty: `(0, 0, 0)` is feasible. -/
theorem mcConstraint_nonempty (hΦ : ManyConsumersTech Φ) {f : (Fin p → ℝ) → (ι → ℝ) → ℝ}
    (hf : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, 0 ≤ f κ θ) {κ : Fin p → ℝ} (hκ : 0 ≤ κ) :
    ((0, 0, 0) : (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)) ∈ mcConstraint Φ f κ :=
  ⟨fun _ => le_rfl, by simpa using hΦ.zero_mem hκ, zero_mem_mcUpper (hf 0 le_rfl)⟩

/-- `κ′ ≥ 0` on the constraint set. -/
theorem mcConstraint_kappa_nonneg (hΦ : ManyConsumersTech Φ) {f : (Fin p → ℝ) → (ι → ℝ) → ℝ}
    {κ : Fin p → ℝ} (hκ : 0 ≤ κ) {q : (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)}
    (hq : q ∈ mcConstraint Φ f κ) : 0 ≤ q.2.2 :=
  (hΦ.nonneg κ hκ _ hq.2.1).2

/-- The bound `Wᵢ(x, z) ≤ bᵢ + βᵢz` from (W2) at `z = 0` and (W3). -/
theorem mc_aggregator_le {W : (Fin l → ℝ) → ℝ → ℝ} {β : ℝ}
    (hW : IsAggregator (Ici (0 : Fin l → ℝ)) W β) :
    ∃ b, 0 ≤ b ∧ ∀ x : Fin l → ℝ, ∀ z : ℝ, 0 ≤ x → 0 ≤ z → W x z ≤ b + β * z := by
  obtain ⟨b, hb⟩ := hW.bounded 0 le_rfl
  refine ⟨|b|, abs_nonneg _, fun x z hx hz => ?_⟩
  have h1 := (abs_le.1 (hW.lipschitz x hx z hz 0 le_rfl)).2
  have h2 := (le_abs_self _).trans ((hb x hx).trans (le_abs_self b))
  rw [sub_zero, abs_of_nonneg hz] at h1
  linarith

/-- The objective is bounded on the constraint set when `f ≤ M`. -/
theorem mcObjective_bddAbove {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} {M : ℝ} (hM : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, f κ θ ≤ M)
    {κ : Fin p → ℝ} (hκ : 0 ≤ κ) {θ : ι → ℝ} (hθ : θ ∈ mcSimplex ι) :
    BddAbove (mcObjective W θ '' mcConstraint Φ f κ) := by
  classical
  choose b hb0 hb using fun i => mc_aggregator_le (hW i)
  refine ⟨∑ i, (b i + β i * M), ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  refine Finset.sum_le_sum fun i _ => ?_
  have hκ' := mcConstraint_kappa_nonneg hΦ hκ hq
  have hz0 : 0 ≤ q.2.1 i := hq.2.2.1 i
  have hzM : q.2.1 i ≤ M := (mcUpper_le hq.2.2 i).trans (hM _ hκ' _ (mc_single_mem_simplex i))
  have h1 := hb i _ _ (hq.1 i) hz0
  have h2 := (hW i).nonneg _ (hq.1 i) _ hz0
  have h3 := mcSimplex_le_one hθ i
  have h4 := hθ.1 i
  have h5 := mul_le_mul_of_nonneg_left hzM (hW i).beta_pos.le
  nlinarith

/-- The objective is nonnegative for `θ ∈ Δᴵ`. -/
theorem mcObjective_nonneg {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) {f : (Fin p → ℝ) → (ι → ℝ) → ℝ}
    {κ : Fin p → ℝ} {θ : ι → ℝ} (hθ : θ ∈ mcSimplex ι) {q : (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)}
    (hq : q ∈ mcConstraint Φ f κ) : 0 ≤ mcObjective W θ q :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hθ.1 i) ((hW i).nonneg _ (hq.1 i) _ (hq.2.2.1 i))

/-- `Tf ≥ 0`. -/
theorem mcOperator_nonneg {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} {M : ℝ} (hM : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, f κ θ ≤ M)
    (hf : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, 0 ≤ f κ θ) {κ : Fin p → ℝ} (hκ : 0 ≤ κ)
    {θ : ι → ℝ} (hθ : θ ∈ mcSimplex ι) : 0 ≤ mcOperator W Φ f κ θ :=
  (mcObjective_nonneg hW hθ (mcConstraint_nonempty hΦ hf hκ)).trans
    (le_csSup (mcObjective_bddAbove hW hΦ hM hκ hθ) ⟨_, mcConstraint_nonempty hΦ hf hκ, rfl⟩)

/-- `Tf` is bounded: `Tf ≤ Σᵢ (bᵢ + βᵢM)` when `f ≤ M`. -/
theorem mcOperator_bdd {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} {M : ℝ} (hM : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, f κ θ ≤ M)
    (hf : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, 0 ≤ f κ θ) :
    ∃ M', ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, mcOperator W Φ f κ θ ≤ M' := by
  classical
  choose b hb0 hb using fun i => mc_aggregator_le (hW i)
  refine ⟨∑ i, (b i + β i * M), fun κ hκ θ hθ => csSup_le
    ⟨_, _, mcConstraint_nonempty hΦ hf hκ, rfl⟩ ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  refine Finset.sum_le_sum fun i _ => ?_
  have hκ' := mcConstraint_kappa_nonneg hΦ hκ hq
  have hz0 : 0 ≤ q.2.1 i := hq.2.2.1 i
  have hzM : q.2.1 i ≤ M := (mcUpper_le hq.2.2 i).trans (hM _ hκ' _ (mc_single_mem_simplex i))
  have h1 := hb i _ _ (hq.1 i) hz0
  have h2 := (hW i).nonneg _ (hq.1 i) _ hz0
  have h3 := mcSimplex_le_one hθ i
  have h4 := hθ.1 i
  have h5 := mul_le_mul_of_nonneg_left hzM (hW i).beta_pos.le
  nlinarith

/-- **`T` maps into support-function-type functions** (the NOTE to Exercise 16.7f):
`Tf(κ, ·)` is the supremum of the linear maps `θ ↦ θ · w` over the attainable vectors
`w = (Wᵢ(γᵢ, z′ᵢ))ᵢ ∈ ℝᴵ₊`, and every such `w` lies in `𝒰_{Tf}(κ)`. -/
theorem mcOperator_supportType {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} {M : ℝ} (hM : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, f κ θ ≤ M)
    (hf : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, 0 ≤ f κ θ) :
    mcSupportType (mcOperator W Φ f) := by
  intro κ hκ θ hθ ε hε
  obtain ⟨_, ⟨q, hq, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup
    (s := mcObjective W θ '' mcConstraint Φ f κ) ⟨_, _, mcConstraint_nonempty hΦ hf hκ, rfl⟩
    (sub_lt_self (mcOperator W Φ f κ θ) hε)
  refine ⟨fun i => W i (q.1 i) (q.2.1 i), ⟨fun i => (hW i).nonneg _ (hq.1 i) _ (hq.2.2.1 i),
    fun θ' hθ' => le_csSup (mcObjective_bddAbove hW hΦ hM hκ hθ') ⟨q, hq, rfl⟩⟩, hlt⟩

/-- `T` maps admissible functions to admissible functions (in fact every bounded nonnegative
`f`). -/
theorem mcOperator_admissible {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} (hf : MCAdmissible f) : MCAdmissible (mcOperator W Φ f) := by
  obtain ⟨M, hM⟩ := hf.bdd
  exact ⟨mcOperator_bdd hW hΦ hM hf.nonneg, fun κ hκ θ hθ => mcOperator_nonneg hW hΦ hM
    hf.nonneg hκ hθ, mcOperator_supportType hW hΦ hM hf.nonneg⟩

/-- **Monotonicity** (Blackwell's first condition): `f ≤ g` implies `Tf ≤ Tg`. -/
theorem mcOperator_mono {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f g : (Fin p → ℝ) → (ι → ℝ) → ℝ} (hf : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, 0 ≤ f κ θ)
    {M : ℝ} (hM : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, g κ θ ≤ M)
    (hfg : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, f κ θ ≤ g κ θ) {κ : Fin p → ℝ} (hκ : 0 ≤ κ)
    {θ : ι → ℝ} (hθ : θ ∈ mcSimplex ι) : mcOperator W Φ f κ θ ≤ mcOperator W Φ g κ θ := by
  refine csSup_le_csSup (mcObjective_bddAbove hW hΦ hM hκ hθ)
    ⟨_, _, mcConstraint_nonempty hΦ hf hκ, rfl⟩ (image_mono fun q hq => ?_)
  have hκ' := mcConstraint_kappa_nonneg hΦ hκ hq
  exact ⟨hq.1, hq.2.1, hq.2.2.1, fun θ' hθ' => (hq.2.2.2 θ' hθ').trans (hfg _ hκ' θ' hθ')⟩

/-! ### Exercise 16.7f: the hint, discounting and the contraction -/

/-- `𝒰_g(κ′)` is compact (closed, and inside `∏ᵢ [0, g(κ′, eᵢ)]`). -/
theorem mcUpper_isCompact {g : (Fin p → ℝ) → (ι → ℝ) → ℝ} {κ' : Fin p → ℝ} :
    IsCompact (mcUpper g κ') := by
  classical
  refine (isCompact_Icc (a := (0 : ι → ℝ)) (b := fun i => g κ' (Pi.single i 1))).of_isClosed_subset
    ?_ fun z hz => ⟨hz.1, fun i => mcUpper_le hz i⟩
  have e : mcUpper g κ' = {z | 0 ≤ z} ∩ ⋂ θ ∈ mcSimplex ι, {z | ∑ i, θ i * z i ≤ g κ' θ} := by
    ext z
    exact ⟨fun h => ⟨h.1, mem_iInter₂.2 h.2⟩, fun h => ⟨h.1, mem_iInter₂.1 h.2⟩⟩
  rw [e]
  exact (isClosed_le continuous_const continuous_id).inter (isClosed_biInter fun θ _ =>
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))
      continuous_const)

/-- `𝒰_g(κ′)` is convex. -/
theorem convex_mcUpper {g : (Fin p → ℝ) → (ι → ℝ) → ℝ} {κ' : Fin p → ℝ} :
    Convex ℝ (mcUpper g κ') := by
  rintro z ⟨hz0, hz⟩ z' ⟨hz0', hz'⟩ a b ha hb hab
  refine ⟨add_nonneg (smul_nonneg ha hz0) (smul_nonneg hb hz0'), fun θ hθ => ?_⟩
  have h1 := mul_le_mul_of_nonneg_left (hz θ hθ) ha
  have h2 := mul_le_mul_of_nonneg_left (hz' θ hθ) hb
  have e : ∑ i, θ i * (a • z + b • z') i = a * ∑ i, θ i * z i + b * ∑ i, θ i * z' i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hg : a * g κ' θ + b * g κ' θ = g κ' θ := by rw [← add_mul, hab, one_mul]
  rw [e]
  linarith

/-- **The hint to Exercise 16.7f, corrected**: `𝒰ᵃ = B`, i.e.
`{z′ ≥ 0 : f(κᵃ, θ′) + a ≥ θ′ · z′ ∀θ′} = {z′ ≥ 0 : z′ ≤ z″ + a𝟙 for some z″ ∈ 𝒰}`, provided
`f(κᵃ, ·) ≥ 0` is of support-function type (false in general: `ex_16_7f_hint_counterexample`).
`B ⊆ 𝒰ᵃ` always; for `⊆`, a point of `𝒰ᵃ` outside `B` would be separated from the closed convex
set `𝒰 + a𝟙 − ℝᴵ₊` by some `θ ∈ Δᴵ`, contradicting `f(κᵃ, θ) = sup_{z ∈ 𝒰} θ · z`. -/
theorem ex_16_7f_hint {g : (Fin p → ℝ) → (ι → ℝ) → ℝ} {κ' : Fin p → ℝ}
    (hg0 : ∀ θ ∈ mcSimplex ι, 0 ≤ g κ' θ)
    (hgs : ∀ θ ∈ mcSimplex ι, ∀ ε > 0, ∃ z ∈ mcUpper g κ', g κ' θ - ε < ∑ i, θ i * z i)
    {a : ℝ} (ha : 0 ≤ a) :
    mcUpper (fun κ θ => g κ θ + a) κ' =
      {z | 0 ≤ z ∧ ∃ z'' ∈ mcUpper g κ', z ≤ z'' + fun _ => a} := by
  ext z
  constructor
  · rintro ⟨hz0, hz⟩
    refine ⟨hz0, ?_⟩
    by_contra hnot
    set D : Set (ι → ℝ) := {w | ∃ k ∈ (fun z'' => z'' + fun _ => a) '' mcUpper g κ', w ≤ k}
    have hzD : z ∉ D := by
      rintro ⟨_, ⟨z'', hz'', rfl⟩, hle⟩
      exact hnot ⟨z'', hz'', hle⟩
    have hDcl : IsClosed D :=
      mc_isClosed_lowerHull (mcUpper_isCompact.image (continuous_id.add continuous_const))
    have hDc : Convex ℝ D := by
      rintro w ⟨_, ⟨k, hk, rfl⟩, hw⟩ w' ⟨_, ⟨k', hk', rfl⟩, hw'⟩ s t hs ht hst
      refine ⟨_, ⟨s • k + t • k', convex_mcUpper hk hk' hs ht hst, rfl⟩, fun i => ?_⟩
      have h1 := mul_le_mul_of_nonneg_left (hw i) hs
      have h2 := mul_le_mul_of_nonneg_left (hw' i) ht
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
      nlinarith
    have hDne : D.Nonempty :=
      ⟨0, _, ⟨0, zero_mem_mcUpper hg0, rfl⟩, fun i => by simp [ha]⟩
    obtain ⟨θ, hθ, r, hD, hr⟩ := mc_exists_simplex_separating hDc hDcl hDne
      (fun w ⟨k, hk, hwk⟩ w' hw' => ⟨k, hk, hw'.trans hwk⟩) hzD
    obtain ⟨z'', hz'', hlt⟩ := hgs θ hθ (∑ i, θ i * z i - r) (by linarith)
    have h1 := hD _ ⟨_, ⟨z'', hz'', rfl⟩, le_rfl⟩
    have e : ∑ i, θ i * ((z'' + fun _ => a : ι → ℝ) i) = ∑ i, θ i * z'' i + a :=
      mc_dot_add_const hθ z'' a
    rw [e] at h1
    have h2 := hz θ hθ
    linarith
  · rintro ⟨hz0, z'', hz'', hle⟩
    refine ⟨hz0, fun θ hθ => ?_⟩
    have h1 : ∑ i, θ i * z i ≤ ∑ i, θ i * (z'' i + a) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (hθ.1 i)
    rw [mc_dot_add_const hθ] at h1
    linarith [hz''.2 θ hθ]

/-- **Discounting** (Blackwell's second condition, corrected): for `f` admissible (in particular
of support-function type) and `a ≥ 0`, `T(f + a) ≤ Tf + βa` with `β ≥ βᵢ` for all `i`. -/
theorem mcOperator_discount {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} (hf : MCAdmissible f) {a : ℝ} (ha : 0 ≤ a) {β0 : ℝ}
    (hβ0 : ∀ i, β i ≤ β0) {κ : Fin p → ℝ} (hκ : 0 ≤ κ) {θ : ι → ℝ} (hθ : θ ∈ mcSimplex ι) :
    mcOperator W Φ (fun κ θ => f κ θ + a) κ θ ≤ mcOperator W Φ f κ θ + β0 * a := by
  obtain ⟨M, hM⟩ := hf.bdd
  have hfa0 : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, 0 ≤ f κ θ + a := fun κ hκ θ hθ =>
    add_nonneg (hf.nonneg κ hκ θ hθ) ha
  refine csSup_le ⟨_, _, mcConstraint_nonempty hΦ hfa0 hκ, rfl⟩ ?_
  rintro _ ⟨q, hq, rfl⟩
  have hκ' := mcConstraint_kappa_nonneg hΦ hκ hq
  have hB : q.2.1 ∈ {z | 0 ≤ z ∧ ∃ z'' ∈ mcUpper f q.2.2, z ≤ z'' + fun _ => a} := by
    rw [← ex_16_7f_hint (hf.nonneg _ hκ') (hf.support _ hκ') ha]
    exact hq.2.2
  obtain ⟨-, z'', hz'', hle⟩ := hB
  have hq'' : ((q.1, z'', q.2.2) : (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)) ∈
      mcConstraint Φ f κ := ⟨hq.1, hq.2.1, hz''⟩
  have hterm : ∀ i, θ i * W i (q.1 i) (q.2.1 i) ≤ θ i * W i (q.1 i) (z'' i) + θ i * (β0 * a) :=
    fun i => by
      have hz0 : 0 ≤ q.2.1 i := hq.2.2.1 i
      have hz''0 : 0 ≤ z'' i := hz''.1 i
      have h1 : W i (q.1 i) (q.2.1 i) ≤ W i (q.1 i) (z'' i + a) :=
        (hW i).mono _ _ _ _ (hq.1 i) le_rfl hz0 (hle i)
      have h2 := (abs_le.1 ((hW i).agg.lipschitz _ (hq.1 i) (z'' i + a) (by linarith) (z'' i)
        hz''0)).2
      rw [show z'' i + a - z'' i = a by ring, abs_of_nonneg ha] at h2
      have h3 : β i * a ≤ β0 * a := mul_le_mul_of_nonneg_right (hβ0 i) ha
      have h4 := mul_le_mul_of_nonneg_left (show W i (q.1 i) (q.2.1 i) ≤
        W i (q.1 i) (z'' i) + β0 * a by linarith) (hθ.1 i)
      linarith
  have hle' : mcObjective W θ q ≤ mcObjective W θ (q.1, z'', q.2.2) + β0 * a := by
    calc mcObjective W θ q ≤ ∑ i, (θ i * W i (q.1 i) (z'' i) + θ i * (β0 * a)) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, hθ.2, one_mul]
          rfl
  exact hle'.trans (add_le_add_left (le_csSup (mcObjective_bddAbove (fun i => (hW i).agg) hΦ hM
    hκ hθ) ⟨_, hq'', rfl⟩) _)

/-- **Exercise 16.7f**, corrected: on admissible functions (bounded, nonnegative, of
support-function type) `T` is a contraction with modulus `β = maxᵢ βᵢ`: `|f − g| ≤ a` implies
`|Tf − Tg| ≤ βa`. (On all of `F` it is not: `ex_16_7f_counterexample`.) -/
theorem ex_16_7f {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f g : (Fin p → ℝ) → (ι → ℝ) → ℝ} (hf : MCAdmissible f) (hg : MCAdmissible g) {a : ℝ}
    (ha : 0 ≤ a) (hfg : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, |f κ θ - g κ θ| ≤ a) {β0 : ℝ}
    (hβ0 : ∀ i, β i ≤ β0) :
    ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι,
      |mcOperator W Φ f κ θ - mcOperator W Φ g κ θ| ≤ β0 * a := by
  intro κ hκ θ hθ
  obtain ⟨Mf, hMf⟩ := hf.bdd
  obtain ⟨Mg, hMg⟩ := hg.bdd
  have h1 : mcOperator W Φ f κ θ ≤ mcOperator W Φ (fun κ θ => g κ θ + a) κ θ :=
    mcOperator_mono (fun i => (hW i).agg) hΦ hf.nonneg (M := Mg + a)
      (fun κ hκ θ hθ => by linarith [hMg κ hκ θ hθ])
      (fun κ hκ θ hθ => by linarith [(abs_le.1 (hfg κ hκ θ hθ)).2]) hκ hθ
  have h2 : mcOperator W Φ g κ θ ≤ mcOperator W Φ (fun κ θ => f κ θ + a) κ θ :=
    mcOperator_mono (fun i => (hW i).agg) hΦ hg.nonneg (M := Mf + a)
      (fun κ hκ θ hθ => by linarith [hMf κ hκ θ hθ])
      (fun κ hκ θ hθ => by linarith [(abs_le.1 (hfg κ hκ θ hθ)).1]) hκ hθ
  have h3 := mcOperator_discount hW hΦ hg ha hβ0 hκ hθ
  have h4 := mcOperator_discount hW hΦ hf ha hβ0 hκ hθ
  rw [abs_le]
  constructor <;> linarith

/-! ### The unique fixed point -/

/-- A pointwise limit of uniformly bounded functions of support-function type is of
support-function type (Bolzano–Weierstrass in `∏ᵢ [0, M]`). So the admissible functions are closed
under pointwise limits. -/
theorem mcSupportType_of_tendsto {F : ℕ → (Fin p → ℝ) → (ι → ℝ) → ℝ}
    {v : (Fin p → ℝ) → (ι → ℝ) → ℝ} (hFs : ∀ n, mcSupportType (F n)) {M : ℝ}
    (hM : ∀ n κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, F n κ θ ≤ M)
    (hlim : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, Tendsto (fun n => F n κ θ) atTop (𝓝 (v κ θ))) :
    mcSupportType v := by
  classical
  intro κ hκ θ hθ ε hε
  choose z hz hzlt using fun n => hFs n κ hκ θ hθ (ε / 2) (half_pos hε)
  have hzI : ∀ n, z n ∈ Icc (0 : ι → ℝ) (fun _ => M) := fun n =>
    ⟨(hz n).1, fun i => (mcUpper_le (hz n) i).trans (hM n κ hκ _ (mc_single_mem_simplex i))⟩
  obtain ⟨z0, hz0I, φ, hφ, hlimz⟩ := isCompact_Icc.tendsto_subseq hzI
  have hdot : ∀ θ' : ι → ℝ, Tendsto (fun n => ∑ i, θ' i * z (φ n) i) atTop
      (𝓝 (∑ i, θ' i * z0 i)) := fun θ' =>
    ((continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)).tendsto
      z0).comp hlimz
  refine ⟨z0, ⟨hz0I.1, fun θ' hθ' => le_of_tendsto_of_tendsto' (hdot θ')
    ((hlim κ hκ θ' hθ').comp hφ.tendsto_atTop) fun n => (hz (φ n)).2 θ' hθ'⟩, ?_⟩
  have := le_of_tendsto_of_tendsto' (((hlim κ hκ θ hθ).comp hφ.tendsto_atTop).sub_const (ε / 2))
    (hdot θ) fun n => (hzlt (φ n)).le
  linarith

/-- **Existence of a solution of (4)** (Exercise 16.7f, corrected): with `βᵢ ≤ β < 1`, the
iterates `Tⁿ0` converge to an admissible `v` with `Tv = v` on `ℝᵖ₊ × Δᴵ`. -/
theorem ex_16_7f_exists_fixed {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) (hΦ : ManyConsumersTech Φ) {β0 : ℝ}
    (hβ0 : ∀ i, β i ≤ β0) (hβ00 : 0 ≤ β0) (hβ1 : β0 < 1) :
    ∃ v, MCAdmissible v ∧ ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, mcOperator W Φ v κ θ = v κ θ := by
  set F : ℕ → (Fin p → ℝ) → (ι → ℝ) → ℝ := fun n => (mcOperator W Φ)^[n] fun _ _ => 0 with hF
  have hF0 : ∀ κ θ, F 0 κ θ = 0 := fun _ _ => rfl
  have hFs : ∀ n, F (n + 1) = mcOperator W Φ (F n) := fun n =>
    Function.iterate_succ_apply' _ _ _
  have hadm0 : MCAdmissible fun (_ : Fin p → ℝ) (_ : ι → ℝ) => (0 : ℝ) :=
    ⟨⟨0, fun _ _ _ _ => le_rfl⟩, fun _ _ _ _ => le_rfl, fun _ _ _ _ ε hε =>
      ⟨0, zero_mem_mcUpper fun _ _ => le_rfl, by simpa using hε⟩⟩
  have hadm : ∀ n, MCAdmissible (F n) := by
    intro n
    induction n with
    | zero => exact hadm0
    | succ n ih => rw [hFs]; exact mcOperator_admissible (fun i => (hW i).agg) hΦ ih
  obtain ⟨M1, hM1⟩ := (hadm 1).bdd
  set C := max M1 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  have hstep : ∀ n, ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, |F (n + 1) κ θ - F n κ θ| ≤ C * β0 ^ n := by
    intro n
    induction n with
    | zero =>
      intro κ hκ θ hθ
      rw [pow_zero, mul_one, hF0, sub_zero, abs_of_nonneg ((hadm 1).nonneg κ hκ θ hθ)]
      exact (hM1 κ hκ θ hθ).trans (le_max_left _ _)
    | succ n ih =>
      intro κ hκ θ hθ
      have e : F (n + 1 + 1) κ θ - F (n + 1) κ θ =
          mcOperator W Φ (F (n + 1)) κ θ - mcOperator W Φ (F n) κ θ := by
        rw [hFs (n + 1), hFs n]
      rw [e]
      have := ex_16_7f hW hΦ (hadm (n + 1)) (hadm n) (by positivity) ih hβ0 κ hκ θ hθ
      calc _ ≤ β0 * (C * β0 ^ n) := this
        _ = C * β0 ^ (n + 1) := by ring
  have hgeom : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι,
      ∀ n, dist (F n κ θ) (F (n + 1) κ θ) ≤ C * β0 ^ n := fun κ hκ θ hθ n => by
    rw [Real.dist_eq, abs_sub_comm]; exact hstep n κ hκ θ hθ
  set v : (Fin p → ℝ) → (ι → ℝ) → ℝ := fun κ θ => limUnder atTop fun n => F n κ θ with hv
  have hlim : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, Tendsto (fun n => F n κ θ) atTop (𝓝 (v κ θ)) :=
    fun κ hκ θ hθ => (cauchySeq_of_le_geometric β0 C hβ1 (hgeom κ hκ θ hθ)).tendsto_limUnder
  have hdist : ∀ n, ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι,
      |F n κ θ - v κ θ| ≤ C * β0 ^ n / (1 - β0) := fun n κ hκ θ hθ => by
    have := dist_le_of_le_geometric_of_tendsto β0 C hβ1 (hgeom κ hκ θ hθ) (hlim κ hκ θ hθ) n
    rwa [Real.dist_eq] at this
  have h1β : 0 < 1 - β0 := by linarith
  have hbound : ∀ n, C * β0 ^ n / (1 - β0) ≤ C / (1 - β0) := fun n =>
    div_le_div_of_nonneg_right (mul_le_of_le_one_right hC0 (pow_le_one₀ hβ00 hβ1.le)) h1β.le
  have hvadm : MCAdmissible v := by
    refine ⟨⟨C / (1 - β0), fun κ hκ θ hθ => ?_⟩, fun κ hκ θ hθ =>
      ge_of_tendsto' (hlim κ hκ θ hθ) fun n => (hadm n).nonneg κ hκ θ hθ,
      mcSupportType_of_tendsto (fun n => (hadm n).support) (M := 2 * (C / (1 - β0)))
        (fun n κ hκ θ hθ => ?_) hlim⟩
    · have := hdist 0 κ hκ θ hθ
      rw [hF0, zero_sub, abs_neg, pow_zero, mul_one] at this
      exact (le_abs_self _).trans this
    · have h0 := hdist 0 κ hκ θ hθ
      have hn := hdist n κ hκ θ hθ
      rw [hF0, zero_sub, abs_neg, pow_zero, mul_one] at h0
      linarith [le_abs_self (v κ θ), le_abs_self (F n κ θ - v κ θ), hbound n]
  refine ⟨v, hvadm, fun κ hκ θ hθ => tendsto_nhds_unique ?_
    ((hlim κ hκ θ hθ).comp (tendsto_add_atTop_nat 1))⟩
  have hT : ∀ n, |F (n + 1) κ θ - mcOperator W Φ v κ θ| ≤ β0 * C / (1 - β0) * β0 ^ n :=
    fun n => by
      rw [hFs n]
      have := ex_16_7f hW hΦ (hadm n) hvadm (by positivity) (hdist n) hβ0 κ hκ θ hθ
      calc _ ≤ β0 * (C * β0 ^ n / (1 - β0)) := this
        _ = β0 * C / (1 - β0) * β0 ^ n := by ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => (Real.norm_eq_abs _).trans_le (hT n)) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ00 hβ1).const_mul (β0 * C / (1 - β0))

/-- **Uniqueness of the solution of (4)** among admissible functions. -/
theorem ex_16_7f_unique {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) (hΦ : ManyConsumersTech Φ) {β0 : ℝ}
    (hβ0 : ∀ i, β i ≤ β0) (hβ00 : 0 ≤ β0) (hβ1 : β0 < 1) {v w : (Fin p → ℝ) → (ι → ℝ) → ℝ}
    (hv : MCAdmissible v) (hw : MCAdmissible w)
    (hTv : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, mcOperator W Φ v κ θ = v κ θ)
    (hTw : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, mcOperator W Φ w κ θ = w κ θ) :
    ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, v κ θ = w κ θ := by
  obtain ⟨Mv, hMv⟩ := hv.bdd
  obtain ⟨Mw, hMw⟩ := hw.bdd
  set a := max Mv 0 + max Mw 0 with ha
  have ha0 : 0 ≤ a := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hbound : ∀ n, ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, |v κ θ - w κ θ| ≤ β0 ^ n * a := by
    intro n
    induction n with
    | zero =>
      intro κ hκ θ hθ
      rw [pow_zero, one_mul, abs_le]
      have := hMv κ hκ θ hθ
      have := hMw κ hκ θ hθ
      have := hv.nonneg κ hκ θ hθ
      have := hw.nonneg κ hκ θ hθ
      have := le_max_left Mv 0
      have := le_max_left Mw 0
      have := le_max_right Mv 0
      have := le_max_right Mw 0
      constructor <;> linarith
    | succ n ih =>
      intro κ hκ θ hθ
      rw [← hTv κ hκ θ hθ, ← hTw κ hκ θ hθ]
      have := ex_16_7f hW hΦ hv hw (by positivity) ih hβ0 κ hκ θ hθ
      calc _ ≤ β0 * (β0 ^ n * a) := this
        _ = β0 ^ (n + 1) * a := by ring
  intro κ hκ θ hθ
  have hlim : Tendsto (fun n => β0 ^ n * a) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ00 hβ1).mul_const a
  have h := ge_of_tendsto' hlim fun n => hbound n κ hκ θ hθ
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h)

/-! ### The support function `v` solves (4); Principle of Optimality -/

/-- The support function `v` of (2) is admissible: bounded, nonnegative, and of support-function
type (it is the support function of `U(κ) ⊆ ℝᴵ₊`, and `U(κ) ⊆ 𝒰_v(κ)`). -/
theorem mcSupport_admissible {W : ι → (Fin l → ℝ) → ℝ → ℝ} {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ) :
    MCAdmissible (mcSupport Φ u) := by
  obtain ⟨B, -, hB⟩ := mc_utility_bounds hu
  refine ⟨⟨∑ i, B i, fun κ hκ θ hθ => csSup_le ((mcUtilSet_nonempty hΦ u hκ).image _) ?_⟩,
    fun κ hκ θ hθ => ?_, fun κ hκ θ hθ ε hε => ?_⟩
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine Finset.sum_le_sum fun i _ => ?_
    have h := hB i _ (hc.1 i)
    have h1 := mcSimplex_le_one hθ i
    nlinarith [hθ.1 i]
  · have h0 := mcFeasible_zero (ι := ι) hΦ hκ
    exact (Finset.sum_nonneg fun i _ => mul_nonneg (hθ.1 i) (hB i _ (h0.1 i)).1).trans
      (le_csSup (mcUtilSet_bddAbove hB κ hθ) ⟨_, ⟨0, h0, rfl⟩, rfl⟩)
  · obtain ⟨_, ⟨z, hz, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup
      ((mcUtilSet_nonempty hΦ u hκ).image fun z => ∑ i, θ i * z i)
      (sub_lt_self (mcSupport Φ u κ θ) hε)
    exact ⟨z, ⟨(mcUtilSet_subset_Icc hB κ hz).1, ex_16_7c_onlyIf hB hz⟩, hlt⟩

/-- **Equation (4)**, p. 498: if every `U(κ′)` is closed, the support function `v` of (2) satisfies
`v = Tv` (by (3) and the corrected Exercise 16.7c, `z′ ∈ U(κ′)` iff `z′ ∈ 𝒰_v(κ′)`). -/
theorem mc_eq4 {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    (hcl : ∀ κ', 0 ≤ κ' → IsClosed (mcUtilSet Φ u κ')) {κ : Fin p → ℝ} (hκ : 0 ≤ κ)
    (θ : ι → ℝ) : mcSupport Φ u κ θ = mcOperator W Φ (mcSupport Φ u) κ θ := by
  rw [mc_eq3 hu hκ θ]
  unfold mcOperator
  congr 1
  ext r
  constructor
  · rintro ⟨γ, z', κ', hγ, hΦκ, hz', rfl⟩
    have hκ' : 0 ≤ κ' := (hΦ.nonneg κ hκ _ hΦκ).2
    exact ⟨(γ, z', κ'), ⟨hγ, hΦκ, (ex_16_7c hW hu hΦ hκ' (hcl κ' hκ') z').1 hz'⟩, rfl⟩
  · rintro ⟨q, ⟨hγ, hΦκ, hz'⟩, rfl⟩
    have hκ' : 0 ≤ q.2.2 := (hΦ.nonneg κ hκ _ hΦκ).2
    exact ⟨q.1, q.2.1, q.2.2, hγ, hΦκ, (ex_16_7c hW hu hΦ hκ' (hcl _ hκ') q.2.1).2 hz', rfl⟩

/-- **The Principle of Optimality question of p. 499**, settled when every `U(κ)` is closed: the
support function `v` of (2) is a fixed point of `T`, and it is the only admissible one; so the
unique solution of (4) delivered by the contraction is the value of the original problem (2). -/
theorem mc_support_unique_fixed {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    {β0 : ℝ} (hβ0 : ∀ i, β i ≤ β0) (hβ00 : 0 ≤ β0) (hβ1 : β0 < 1)
    (hcl : ∀ κ', 0 ≤ κ' → IsClosed (mcUtilSet Φ u κ')) :
    (∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι,
      mcOperator W Φ (mcSupport Φ u) κ θ = mcSupport Φ u κ θ) ∧
    ∀ w, MCAdmissible w → (∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, mcOperator W Φ w κ θ = w κ θ) →
      ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι, w κ θ = mcSupport Φ u κ θ := by
  have hfix : ∀ κ, 0 ≤ κ → ∀ θ ∈ mcSimplex ι,
      mcOperator W Φ (mcSupport Φ u) κ θ = mcSupport Φ u κ θ := fun κ hκ θ _ =>
    (mc_eq4 hW hu hΦ hcl hκ θ).symm
  exact ⟨hfix, fun w hw hTw => ex_16_7f_unique hW hΦ hβ0 hβ00 hβ1 hw
    (mcSupport_admissible hu hΦ) hTw hfix⟩

/-! ### Exercises 16.7d and 16.7g -/

/-- The objective of (4) is continuous on the constraint set. -/
theorem mcObjective_continuousOn {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i))
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} {κ : Fin p → ℝ} (θ : ι → ℝ) :
    ContinuousOn (mcObjective W θ) (mcConstraint Φ f κ) := by
  refine continuousOn_finsetSum _ fun i _ => continuousOn_const.mul ?_
  have hmaps : MapsTo (fun q : (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ) => (q.1 i, q.2.1 i))
      (mcConstraint Φ f κ) (Ici 0 ×ˢ Ici 0) := fun q hq => ⟨hq.1 i, hq.2.2.1 i⟩
  exact (hW i).continuousOn.comp (((continuous_apply i).comp continuous_fst).prodMk
    ((continuous_apply i).comp (continuous_fst.comp continuous_snd))).continuousOn hmaps

/-- **Exercise 16.7d**, compactness: for `f ∈ F` and `κ ≥ 0` the constraint set of (4) is compact
(`Φ(κ)` is compact, `0 ≤ z′ᵢ ≤ f(κ′, eᵢ) ≤ ‖f‖`, and it is closed since `f` is continuous). -/
theorem ex_16_7d_compact (hΦ : ManyConsumersTech Φ) {f : (Fin p → ℝ) → (ι → ℝ) → ℝ}
    (hf : MCInF f) {κ : Fin p → ℝ} (hκ : 0 ≤ κ) : IsCompact (mcConstraint Φ f κ) := by
  classical
  obtain ⟨M, hM⟩ := hf.bdd
  have hK := hΦ.compact κ hκ
  have hbdd : ∀ m : Fin l, BddAbove ((fun q : (Fin l → ℝ) × (Fin p → ℝ) => q.1 m) '' Φ κ) :=
    fun m => (hK.image ((continuous_apply m).comp continuous_fst)).bddAbove
  choose g hg using hbdd
  have hsub : mcConstraint Φ f κ ⊆ Icc (0 : ι → Fin l → ℝ) (fun _ => g) ×ˢ
      (Icc (0 : ι → ℝ) (fun _ => M) ×ˢ (Prod.snd '' Φ κ)) := by
    intro q hq
    have hκ' := mcConstraint_kappa_nonneg hΦ hκ hq
    refine ⟨⟨hq.1, fun i => ?_⟩, ⟨hq.2.2.1, fun i => (mcUpper_le hq.2.2 i).trans
      (hM _ hκ' _ (mc_single_mem_simplex i))⟩, ⟨_, hq.2.1, rfl⟩⟩
    calc q.1 i ≤ ∑ j, q.1 j := Finset.single_le_sum (fun j _ => hq.1 j) (Finset.mem_univ i)
      _ ≤ g := fun m => hg m ⟨_, hq.2.1, rfl⟩
  refine (isCompact_Icc.prod (isCompact_Icc.prod (hK.image continuous_snd))).of_isClosed_subset
    ?_ hsub
  refine isClosed_of_closure_subset fun q hq => ?_
  obtain ⟨qs, hqs, hlim⟩ := mem_closure_iff_seq_limit.1 hq
  have h1 : Tendsto (fun n => (qs n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto _).comp hlim
  have h2 : Tendsto (fun n => (qs n).2.1) atTop (𝓝 q.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have h3 : Tendsto (fun n => (qs n).2.2) atTop (𝓝 q.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  have hγ : ∀ i, 0 ≤ q.1 i := fun i =>
    ge_of_tendsto' (((continuous_apply i).tendsto _).comp h1) fun n => (hqs n).1 i
  have hsum : Tendsto (fun n => ∑ i, (qs n).1 i) atTop (𝓝 (∑ i, q.1 i)) :=
    ((continuous_finsetSum _ fun i _ => continuous_apply i).tendsto _).comp h1
  have hΦq : (∑ i, q.1 i, q.2.2) ∈ Φ κ :=
    hK.isClosed.mem_of_tendsto (hsum.prodMk_nhds h3) (Eventually.of_forall fun n => (hqs n).2.1)
  have hκ' : 0 ≤ q.2.2 := (hΦ.nonneg κ hκ _ hΦq).2
  refine ⟨hγ, hΦq, ge_of_tendsto' h2 fun n => (hqs n).2.2.1, fun θ hθ => ?_⟩
  have hfθ : Tendsto (fun n => f (qs n).2.2 θ) atTop (𝓝 (f q.2.2 θ)) := by
    have hcont := hf.cont (q.2.2, θ) ⟨hκ', hθ⟩
    have hin : Tendsto (fun n => ((qs n).2.2, θ)) atTop (𝓝[Ici 0 ×ˢ mcSimplex ι] (q.2.2, θ)) :=
      tendsto_nhdsWithin_iff.2 ⟨h3.prodMk_nhds tendsto_const_nhds,
        Eventually.of_forall fun n => ⟨mcConstraint_kappa_nonneg hΦ hκ (hqs n), hθ⟩⟩
    exact hcont.tendsto.comp hin
  exact le_of_tendsto_of_tendsto' (((continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_apply i)).tendsto _).comp h2) hfθ
    fun n => (hqs n).2.2.2 θ hθ

/-- **Exercise 16.7d**, the maximum is attained: for `f ∈ F`, `κ ≥ 0`, the continuous objective
attains its supremum `Tf(κ, θ)` on the compact constraint set. -/
theorem ex_16_7d_exists_max {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, IsAggregator (Ici (0 : Fin l → ℝ)) (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} (hf : MCInF f) {κ : Fin p → ℝ} (hκ : 0 ≤ κ)
    (θ : ι → ℝ) :
    ∃ q ∈ mcConstraint Φ f κ, (∀ q' ∈ mcConstraint Φ f κ, mcObjective W θ q' ≤ mcObjective W θ q)
      ∧ mcOperator W Φ f κ θ = mcObjective W θ q := by
  obtain ⟨q, hq, hmax⟩ := (ex_16_7d_compact hΦ hf hκ).exists_isMaxOn
    ⟨_, mcConstraint_nonempty hΦ hf.nonneg hκ⟩ (mcObjective_continuousOn hW θ)
  have hmax' := isMaxOn_iff.1 hmax
  exact ⟨q, hq, hmax', IsGreatest.csSup_eq ⟨⟨q, hq, rfl⟩, by
    rintro _ ⟨q', hq', rfl⟩; exact hmax' q' hq'⟩⟩

/-- **Exercise 16.7d**, convexity, corrected: the constraint set is convex when every
`f(·, θ′)` is concave on `ℝᵖ₊` (false for general `f ∈ F`: `ex_16_7d_counterexample`). -/
theorem ex_16_7d_convex (hΦ : ManyConsumersTech Φ) {f : (Fin p → ℝ) → (ι → ℝ) → ℝ}
    (hconc : ∀ θ ∈ mcSimplex ι, ConcaveOn ℝ (Ici 0) fun κ' => f κ' θ) {κ : Fin p → ℝ}
    (hκ : 0 ≤ κ) : Convex ℝ (mcConstraint Φ f κ) := by
  rintro q ⟨hq1, hq2, hq30, hq3⟩ q' ⟨hq1', hq2', hq30', hq3'⟩ a b ha hb hab
  have hκ1 := (hΦ.nonneg κ hκ _ hq2).2
  have hκ2 := (hΦ.nonneg κ hκ _ hq2').2
  refine ⟨fun i => ?_, ?_, ?_, fun θ hθ => ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply]
    exact add_nonneg (smul_nonneg ha (hq1 i)) (smul_nonneg hb (hq1' i))
  · have := hΦ.convex κ hκ hq2 hq2' ha hb hab
    convert this using 1
    simp [Finset.sum_add_distrib, Finset.smul_sum]
  · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst]
    exact add_nonneg (smul_nonneg ha hq30) (smul_nonneg hb hq30')
  · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left (hq3 θ hθ) ha
    have h2 := mul_le_mul_of_nonneg_left (hq3' θ hθ) hb
    have h3 := (hconc θ hθ).2 hκ1 hκ2 ha hb hab
    simp only [smul_eq_mul] at h3
    have e : ∑ i, θ i * (a * q.2.1 i + b * q'.2.1 i) =
        a * ∑ i, θ i * q.2.1 i + b * ∑ i, θ i * q'.2.1 i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    linarith

/-- The objective of (4) is concave on the constraint set (W5, `θ ≥ 0`). -/
theorem mcObjective_concave {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {θ : ι → ℝ} (hθ : θ ∈ mcSimplex ι)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ} {κ : Fin p → ℝ}
    {q q' : (ι → Fin l → ℝ) × (ι → ℝ) × (Fin p → ℝ)} (hq : q ∈ mcConstraint Φ f κ)
    (hq' : q' ∈ mcConstraint Φ f κ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * mcObjective W θ q + b * mcObjective W θ q' ≤ mcObjective W θ (a • q + b • q') := by
  unfold mcObjective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := (hW i).concave.2 (x := (q.1 i, q.2.1 i)) (y := (q'.1 i, q'.2.1 i))
    ⟨hq.1 i, hq.2.2.1 i⟩ ⟨hq'.1 i, hq'.2.2.1 i⟩ ha hb hab
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h
  simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  have := mul_le_mul_of_nonneg_left h (hθ.1 i)
  nlinarith

/-- **Exercise 16.7g**, convexity, for `f` concave in `κ′`: the set of maximisers of (4) is
convex (a concave objective on a convex set). It is not single-valued in general: `W` is concave,
not strictly. -/
theorem ex_16_7g_convex_of_concave {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) (hΦ : ManyConsumersTech Φ)
    {f : (Fin p → ℝ) → (ι → ℝ) → ℝ}
    (hconc : ∀ θ ∈ mcSimplex ι, ConcaveOn ℝ (Ici 0) fun κ' => f κ' θ)
    {κ : Fin p → ℝ} (hκ : 0 ≤ κ) {θ : ι → ℝ} (hθ : θ ∈ mcSimplex ι) :
    Convex ℝ {q ∈ mcConstraint Φ f κ |
      ∀ q' ∈ mcConstraint Φ f κ, mcObjective W θ q' ≤ mcObjective W θ q} := by
  rintro q ⟨hq, hqmax⟩ q' ⟨hq', hq'max⟩ a b ha hb hab
  refine ⟨ex_16_7d_convex hΦ hconc hκ hq hq' ha hb hab, fun q'' hq'' => ?_⟩
  have h1 := mul_le_mul_of_nonneg_left (hqmax q'' hq'') ha
  have h2 := mul_le_mul_of_nonneg_left (hq'max q'' hq'') hb
  have h3 := mcObjective_concave hW hθ hq hq' ha hb hab
  have h4 : a * mcObjective W θ q'' + b * mcObjective W θ q'' = mcObjective W θ q'' := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- The support function `v(·, θ)` of (2) is concave on `ℝᵖ₊` ((T5) and (W5)). -/
theorem mcSupport_concave {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    {θ : ι → ℝ} (hθ : θ ∈ mcSimplex ι) : ConcaveOn ℝ (Ici 0) fun κ => mcSupport Φ u κ θ := by
  obtain ⟨B, -, hB⟩ := mc_utility_bounds hu
  refine ⟨convex_Ici 0, fun κ hκ κ' hκ' a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨_, ⟨_, ⟨c, hc, rfl⟩, rfl⟩, h1⟩ := exists_lt_of_lt_csSup
    ((mcUtilSet_nonempty hΦ u hκ).image fun z => ∑ i, θ i * z i)
    (sub_lt_self (mcSupport Φ u κ θ) hε)
  obtain ⟨_, ⟨_, ⟨c', hc', rfl⟩, rfl⟩, h2⟩ := exists_lt_of_lt_csSup
    ((mcUtilSet_nonempty hΦ u hκ').image fun z => ∑ i, θ i * z i)
    (sub_lt_self (mcSupport Φ u κ' θ) hε)
  have hfeas : mcFeasible Φ (a • κ + b • κ') (fun i => a • c i + b • c' i) := by
    refine ⟨fun i => convex_seqSet (convex_Ici 0) (hc.1 i) (hc'.1 i) ha hb hab, ?_⟩
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum]
    exact mcProdSet_combo hΦ hc.2 hc'.2 ha hb hab
  have hle := le_csSup (mcUtilSet_bddAbove hB (a • κ + b • κ') hθ) ⟨_, ⟨_, hfeas, rfl⟩, rfl⟩
  have hconc : a * ∑ i, θ i * u i (c i) + b * ∑ i, θ i * u i (c' i) ≤
      ∑ i, θ i * u i (a • c i + b • c' i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain rfl : b = 1 - a := by linarith
    have h := mc_utility_concave (hW i) (hu i) _ (hc.1 i) _ (hc'.1 i) a ha (by linarith)
    have := mul_le_mul_of_nonneg_left h (hθ.1 i)
    nlinarith
  have e1 := mul_le_mul_of_nonneg_left h1.le ha
  have e2 := mul_le_mul_of_nonneg_left h2.le hb
  have e3 : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
  change a * mcSupport Φ u κ θ + b * mcSupport Φ u κ' θ ≤
    sSup ((fun z => ∑ i, θ i * z i) '' mcUtilSet Φ u (a • κ + b • κ')) + ε
  nlinarith

/-- **Exercise 16.7g**, convexity, corrected: for `f = v`, the support function of (2) (concave in
`κ`), the policy correspondence of (4) is convex-valued. (Upper hemicontinuity:
`ex_16_7g_support` in `ManyConsumersBerge`.) -/
theorem ex_16_7g {W : ι → (Fin l → ℝ) → ℝ → ℝ} {β : ι → ℝ}
    (hW : ∀ i, ManyConsumersAggregator (W i) (β i)) {u : ι → BddSeq (Fin l → ℝ) → ℝ}
    (hu : ∀ i, IsAggregatorFixedPoint (Ici 0) (W i) (u i)) (hΦ : ManyConsumersTech Φ)
    {κ : Fin p → ℝ} (hκ : 0 ≤ κ) {θ : ι → ℝ} (hθ : θ ∈ mcSimplex ι) :
    Convex ℝ {q ∈ mcConstraint Φ (mcSupport Φ u) κ |
      ∀ q' ∈ mcConstraint Φ (mcSupport Φ u) κ, mcObjective W θ q' ≤ mcObjective W θ q} :=
  ex_16_7g_convex_of_concave hW hΦ (fun _ hθ' => mcSupport_concave hW hu hΦ hθ') hκ hθ

end StokeyLucasPrescott.EquilibriumApplications
