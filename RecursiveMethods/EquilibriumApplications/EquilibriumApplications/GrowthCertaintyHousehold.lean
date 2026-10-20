/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.GrowthCertaintyRecursive

/-!
# The one-sector model under certainty: the household's functional equation (2)

SLP §16.1, p. 479, Exercise 16.1(e). The household with assets `a ≥ 0` in state
`k ∈ K = [a₀, k_max]` solves (2): `Ω(k, a) = max_{0 ≤ a′ ≤ a/q(k)} {U[a − q(k)a′] + β Ω[g(k), a′]}`.

* `GcHouseholdData`: `U` bounded and continuous on `ℝ₊`, `g : K → K` and `q : K → (0, ∞)`
  continuous.
* `gcHhT`, `gcHhTB`: the operator of (2) on bounded continuous functions on `K × ℝ₊`, as a maximum
  over `a′ = s a/q(k)`, `s ∈ [0, 1]`; `gcHhT_ge`, `gcHhT_attained`.
* `gc_hhBellman_unique`: at most one bounded solution of (2) (`|Ω − Ω′| ≤ βⁿ C`).
* `gc_hhTB_contracting`: `T` is a contraction of modulus `β` (Blackwell).
* **Exercise 16.1(e), household** (`ex_16_1e_household`): there is exactly one bounded continuous
  `Ω` satisfying (2); `Ω(k, ·)` is concave; with `U` strictly concave the policy `ω` is
  single-valued and continuous.

**Correction (NOTE to Ex 16.1e).** `ω` single-valued needs only concavity of `Ω(k′, ·)` (not
strict), because `U(a − q a′)` is strictly concave in `a′`; this is how it is proved here.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped BoundedContinuousFunction

variable {a kmax : ℝ}

variable (U : ℝ → ℝ) (g : Icc a kmax → Icc a kmax) (q : Icc a kmax → ℝ) in
/-- The data of (2): `U` bounded and continuous on `ℝ₊`, `g : K → K` and `q : K → (0, ∞)`
continuous, `0 < β < 1`. -/
structure GcHouseholdData (β : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  U_bdd : ∃ B, ∀ x, 0 ≤ x → |U x| ≤ B
  U_cont : ContinuousOn U (Ici 0)
  g_cont : Continuous g
  q_cont : Continuous q
  q_pos : ∀ k, 0 < q k

/-- The household's choice `a′ = s a/q(k)` (made nonnegative for all `s`). -/
noncomputable def gcAc (q : Icc a kmax → ℝ) (k : Icc a kmax) (x : Ici (0 : ℝ)) (s : ℝ) :
    Ici (0 : ℝ) :=
  ⟨max 0 (s * x / q k), mem_Ici.2 (le_max_left _ _)⟩

/-- The objective of (2) at `(k, a)` with `a′ = s a/q(k)` (`U` evaluated at the positive part of
consumption, which is consumption itself for `s ∈ [0, 1]`). -/
noncomputable def gcHhObj (U : ℝ → ℝ) (g : Icc a kmax → Icc a kmax) (q : Icc a kmax → ℝ) (β : ℝ)
    (Ω : Icc a kmax × Ici (0 : ℝ) → ℝ) (p : Icc a kmax × Ici (0 : ℝ)) (s : ℝ) : ℝ :=
  U (max (p.2 - q p.1 * gcAc q p.1 p.2 s) 0) + β * Ω (g p.1, gcAc q p.1 p.2 s)

/-- **The operator of (2)**: `(TΩ)(k, a) = max_{s ∈ [0,1]} {U((1 − s)a) + β Ω(g(k), s a/q(k))}`. -/
noncomputable def gcHhT (U : ℝ → ℝ) (g : Icc a kmax → Icc a kmax) (q : Icc a kmax → ℝ) (β : ℝ)
    (Ω : Icc a kmax × Ici (0 : ℝ) → ℝ) (p : Icc a kmax × Ici (0 : ℝ)) : ℝ :=
  sSup (gcHhObj U g q β Ω p '' Icc 0 1)

/-- `Ω` **satisfies (2)** (with "max"). -/
def GcHouseholdBellman (U : ℝ → ℝ) (g : Icc a kmax → Icc a kmax) (q : Icc a kmax → ℝ) (β : ℝ)
    (Ω : Icc a kmax × Ici (0 : ℝ) → ℝ) : Prop :=
  ∀ p : Icc a kmax × Ici (0 : ℝ),
    (∀ a' : Ici (0 : ℝ), q p.1 * a' ≤ p.2 → U (p.2 - q p.1 * a') + β * Ω (g p.1, a') ≤ Ω p) ∧
    ∃ a' : Ici (0 : ℝ), q p.1 * a' ≤ p.2 ∧ Ω p = U (p.2 - q p.1 * a') + β * Ω (g p.1, a')

variable {U : ℝ → ℝ} {g : Icc a kmax → Icc a kmax} {q : Icc a kmax → ℝ} {β : ℝ}

/-- For `s ∈ [0, 1]`, `a′ = s a/q(k)`. -/
theorem gcAc_val (D : GcHouseholdData U g q β) (k : Icc a kmax) (x : Ici (0 : ℝ)) {s : ℝ}
    (hs : s ∈ Icc 0 1) : (gcAc q k x s : ℝ) = s * x / q k := by
  have : 0 ≤ s * x / q k := div_nonneg (mul_nonneg hs.1 x.2) (D.q_pos k).le
  simp [gcAc, max_eq_right this]

/-- For `s ∈ [0, 1]`, consumption is `a − q(k) a′ = (1 − s) a ≥ 0`. -/
theorem gcAc_cons (D : GcHouseholdData U g q β) (k : Icc a kmax) (x : Ici (0 : ℝ)) {s : ℝ}
    (hs : s ∈ Icc 0 1) : (x : ℝ) - q k * gcAc q k x s = (1 - s) * x := by
  rw [gcAc_val D k x hs]
  field_simp [(D.q_pos k).ne']

/-- `U` composed with the positive part is continuous. -/
theorem GcHouseholdData.continuous_Ue (D : GcHouseholdData U g q β) :
    Continuous fun c : ℝ => U (max c 0) :=
  D.U_cont.comp_continuous (continuous_id.max continuous_const) fun c => le_max_right c 0

/-- The objective of (2) is jointly continuous for continuous `Ω`. -/
theorem gcHhObj_continuous (D : GcHouseholdData U g q β) {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ}
    (hΩ : Continuous Ω) :
    Continuous fun r : (Icc a kmax × Ici (0 : ℝ)) × ℝ => gcHhObj U g q β Ω r.1 r.2 := by
  have hq : Continuous fun r : (Icc a kmax × Ici (0 : ℝ)) × ℝ => q r.1.1 :=
    D.q_cont.comp (continuous_fst.comp continuous_fst)
  have hac : Continuous fun r : (Icc a kmax × Ici (0 : ℝ)) × ℝ => gcAc q r.1.1 r.1.2 r.2 :=
    continuous_induced_rng.2 (show Continuous fun r : (Icc a kmax × Ici (0 : ℝ)) × ℝ =>
      max 0 (r.2 * (r.1.2 : ℝ) / q r.1.1) from continuous_const.max ((continuous_snd.mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).div hq
      fun r => (D.q_pos _).ne'))
  unfold gcHhObj
  exact (D.continuous_Ue.comp ((continuous_subtype_val.comp (continuous_snd.comp
    continuous_fst)).sub (hq.mul (continuous_subtype_val.comp hac)))).add
    (continuous_const.mul (hΩ.comp ((D.g_cont.comp (continuous_fst.comp continuous_fst)).prodMk
      hac)))

/-- The objective of (2) is bounded above on `s ∈ [0, 1]`. -/
theorem gcHhObj_bddAbove (D : GcHouseholdData U g q β) {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ}
    (hΩ : Continuous Ω) (p : Icc a kmax × Ici (0 : ℝ)) :
    BddAbove (gcHhObj U g q β Ω p '' Icc 0 1) :=
  (isCompact_Icc.image ((gcHhObj_continuous D hΩ).comp
    (continuous_const.prodMk continuous_id))).bddAbove

/-- `TΩ` dominates every feasible choice in (2). -/
theorem gcHhT_ge (D : GcHouseholdData U g q β) {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ}
    (hΩ : Continuous Ω) (p : Icc a kmax × Ici (0 : ℝ)) (a' : Ici (0 : ℝ))
    (ha' : q p.1 * a' ≤ p.2) : U (p.2 - q p.1 * a') + β * Ω (g p.1, a') ≤ gcHhT U g q β Ω p := by
  have hq := D.q_pos p.1
  have ha0 : (0 : ℝ) ≤ a' := a'.2
  set s := q p.1 * a' / p.2 with hs
  have hx0 : (0 : ℝ) ≤ p.2 := p.2.2
  have hsm : s ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (mul_nonneg hq.le ha0) hx0, div_le_one_of_le₀ ha' hx0⟩
  have hac : gcAc q p.1 p.2 s = a' := by
    apply Subtype.ext
    rw [gcAc_val D p.1 p.2 hsm]
    rcases hx0.lt_or_eq with hlt | heq
    · rw [hs]
      field_simp
    · have h0 : q p.1 * a' ≤ 0 := ha'.trans heq.symm.le
      have : (a' : ℝ) = 0 := le_antisymm (by nlinarith) ha0
      rw [this, ← heq, mul_zero, zero_div]
  have hc : max ((p.2 : ℝ) - q p.1 * a') 0 = p.2 - q p.1 * a' := max_eq_left (by linarith)
  have := le_csSup (gcHhObj_bddAbove D hΩ p) (mem_image_of_mem _ hsm)
  rwa [gcHhObj, hac, hc] at this

/-- The maximum in (2) is attained. -/
theorem gcHhT_attained (D : GcHouseholdData U g q β) {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ}
    (hΩ : Continuous Ω) (p : Icc a kmax × Ici (0 : ℝ)) :
    ∃ a' : Ici (0 : ℝ), q p.1 * a' ≤ p.2 ∧
      gcHhT U g q β Ω p = U (p.2 - q p.1 * a') + β * Ω (g p.1, a') := by
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_sSup_image_eq (nonempty_Icc.2 zero_le_one)
    ((gcHhObj_continuous D hΩ).comp (continuous_const.prodMk continuous_id)).continuousOn
  have hcons := gcAc_cons D p.1 p.2 hs
  have hx0 : (0 : ℝ) ≤ p.2 := p.2.2
  have hc0 : (0 : ℝ) ≤ p.2 - q p.1 * gcAc q p.1 p.2 s := by
    rw [hcons]; exact mul_nonneg (by linarith [hs.2]) hx0
  refine ⟨gcAc q p.1 p.2 s, by linarith, hmax.trans ?_⟩
  change gcHhObj U g q β Ω p s = _
  rw [gcHhObj, max_eq_left hc0]

/-- `TΩ` is continuous. -/
theorem gcHhT_continuous (D : GcHouseholdData U g q β) {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ}
    (hΩ : Continuous Ω) : Continuous (gcHhT U g q β Ω) :=
  isCompact_Icc.continuous_sSup (gcHhObj_continuous D hΩ)

/-- `|TΩ| ≤ B + β ‖Ω‖`. -/
theorem gcHhT_abs_le (D : GcHouseholdData U g q β) {B : ℝ} (hB : ∀ x, 0 ≤ x → |U x| ≤ B)
    {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ} (hΩ : Continuous Ω) {C : ℝ} (hC : ∀ p, |Ω p| ≤ C)
    (p : Icc a kmax × Ici (0 : ℝ)) : |gcHhT U g q β Ω p| ≤ B + β * C := by
  have hβ := D.beta_pos
  have hbd : ∀ a' : Ici (0 : ℝ), q p.1 * a' ≤ p.2 →
      |U (p.2 - q p.1 * a') + β * Ω (g p.1, a')| ≤ B + β * C := fun a' ha' => by
    have h1 := hB _ (by linarith : (0 : ℝ) ≤ p.2 - q p.1 * a')
    have h2 := hC (g p.1, a')
    calc |U (p.2 - q p.1 * a') + β * Ω (g p.1, a')|
        ≤ |U (p.2 - q p.1 * a')| + |β * Ω (g p.1, a')| := abs_add_le _ _
      _ = |U (p.2 - q p.1 * a')| + β * |Ω (g p.1, a')| := by rw [abs_mul, abs_of_pos hβ]
      _ ≤ B + β * C := add_le_add h1 (mul_le_mul_of_nonneg_left h2 hβ.le)
  obtain ⟨a', ha', e⟩ := gcHhT_attained D hΩ p
  rw [e]
  exact hbd a' ha'

/-- The operator of (2) on bounded continuous functions on `K × ℝ₊`. -/
noncomputable def gcHhTB (D : GcHouseholdData U g q β) (Ω : Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ) :
    Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (gcHhT U g q β Ω) (gcHhT_continuous D Ω.continuous)
    (Classical.choose D.U_bdd + β * ‖Ω‖) fun p => by
      rw [Real.norm_eq_abs]
      exact gcHhT_abs_le D (Classical.choose_spec D.U_bdd) Ω.continuous
        (fun p => by rw [← Real.norm_eq_abs]; exact Ω.norm_coe_le_norm p) p

/-- Values of `gcHhTB`. -/
theorem gcHhTB_apply (D : GcHouseholdData U g q β) (Ω : Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ)
    (p : Icc a kmax × Ici (0 : ℝ)) : gcHhTB D Ω p = gcHhT U g q β Ω p := rfl

/-- One step of `T`: `|TΩ − TΩ′|(k, a) ≤ β C` when `|Ω − Ω′| ≤ C` at all `(g(k), a′)`. -/
theorem gcHhT_sub_le (D : GcHouseholdData U g q β) {Ω Ω' : Icc a kmax × Ici (0 : ℝ) → ℝ}
    (hΩ : Continuous Ω) (hΩ' : Continuous Ω') (p : Icc a kmax × Ici (0 : ℝ)) {C : ℝ}
    (hC : ∀ a', |Ω (g p.1, a') - Ω' (g p.1, a')| ≤ C) :
    |gcHhT U g q β Ω p - gcHhT U g q β Ω' p| ≤ β * C := by
  obtain ⟨a₁, ha₁, h1⟩ := gcHhT_attained D hΩ p
  obtain ⟨a₂, ha₂, h2⟩ := gcHhT_attained D hΩ' p
  have c1 := gcHhT_ge D hΩ' p a₁ ha₁
  have c2 := gcHhT_ge D hΩ p a₂ ha₂
  have b1 := (abs_le.1 (hC a₁)).2
  have b2 := (abs_le.1 (hC a₂)).1
  have hβ := D.beta_pos
  refine abs_le.2 ⟨?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left b2 hβ.le]
  · nlinarith [mul_le_mul_of_nonneg_left b1 hβ.le]

/-- **Blackwell**: the operator of (2) is a contraction of modulus `β`. -/
theorem gc_hhTB_contracting (D : GcHouseholdData U g q β) :
    ContractingWith ⟨β, D.beta_pos.le⟩ (gcHhTB D) := by
  refine ⟨D.beta_lt_one, LipschitzWith.of_dist_le_mul fun Ω Ω' => ?_⟩
  refine (BoundedContinuousFunction.dist_le (mul_nonneg D.beta_pos.le dist_nonneg)).2 fun p => ?_
  rw [Real.dist_eq, gcHhTB_apply, gcHhTB_apply]
  exact gcHhT_sub_le D Ω.continuous Ω'.continuous p fun a' => by
    rw [← Real.dist_eq]; exact BoundedContinuousFunction.dist_coe_le_dist _

/-- At most one bounded solution of (2): `|Ω − Ω′| ≤ βⁿ C` for every `n`. -/
theorem gc_hhBellman_unique (D : GcHouseholdData U g q β) {Ω Ω' : Icc a kmax × Ici (0 : ℝ) → ℝ}
    (hΩ : GcHouseholdBellman U g q β Ω) (hΩ' : GcHouseholdBellman U g q β Ω') {C : ℝ}
    (hC : ∀ p, |Ω p - Ω' p| ≤ C) : Ω = Ω' := by
  have key : ∀ n p, |Ω p - Ω' p| ≤ β ^ n * C := by
    intro n
    induction n with
    | zero => intro p; rw [pow_zero, one_mul]; exact hC p
    | succ n ih =>
      intro p
      obtain ⟨a₁, ha₁, e₁⟩ := (hΩ p).2
      obtain ⟨a₂, ha₂, e₂⟩ := (hΩ' p).2
      have c1 := (hΩ' p).1 a₁ ha₁
      have c2 := (hΩ p).1 a₂ ha₂
      have b1 := (abs_le.1 (ih (g p.1, a₁))).2
      have b2 := (abs_le.1 (ih (g p.1, a₂))).1
      have hβ := D.beta_pos
      rw [pow_succ, mul_comm (β ^ n) β, mul_assoc]
      refine abs_le.2 ⟨?_, ?_⟩
      · nlinarith [mul_le_mul_of_nonneg_left b2 hβ.le]
      · nlinarith [mul_le_mul_of_nonneg_left b1 hβ.le]
  funext p
  have hlim : Tendsto (fun n : ℕ => β ^ n * C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one D.beta_pos.le D.beta_lt_one).mul_const C
  have : |Ω p - Ω' p| ≤ 0 := ge_of_tendsto' hlim fun n => key n p
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-- A fixed point of `T` satisfies (2). -/
theorem gc_hhBellman_of_fixed (D : GcHouseholdData U g q β) {Ω : Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ}
    (hΩ : gcHhTB D Ω = Ω) : GcHouseholdBellman U g q β Ω := fun p => by
  have hp : Ω p = gcHhT U g q β Ω p := by rw [← gcHhTB_apply D Ω p, hΩ]
  refine ⟨fun a' ha' => hp ▸ gcHhT_ge D Ω.continuous p a' ha', ?_⟩
  obtain ⟨a', ha', h⟩ := gcHhT_attained D Ω.continuous p
  exact ⟨a', ha', hp.trans h⟩

/-! ### Concavity of `Ω(k, ·)` and the household's policy -/

/-- `Ω(k, ·)` is concave on `ℝ₊`. -/
def GcConcaveA (Ω : Icc a kmax × Ici (0 : ℝ) → ℝ) : Prop :=
  ∀ (k : Icc a kmax) (x₁ x₂ x : Ici (0 : ℝ)) (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
    (x : ℝ) = θ * x₁ + (1 - θ) * x₂ → θ * Ω (k, x₁) + (1 - θ) * Ω (k, x₂) ≤ Ω (k, x)

/-- The convex combination `θ x₁ + (1 − θ) x₂` in `ℝ₊`. -/
def gcAcombo (x₁ x₂ : Ici (0 : ℝ)) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : Ici (0 : ℝ) :=
  ⟨θ * x₁ + (1 - θ) * x₂, by
    exact mem_Ici.2 (add_nonneg (mul_nonneg h0 x₁.2) (mul_nonneg (by linarith) x₂.2))⟩

/-- `T` preserves concavity in `a` when `U` is concave. -/
theorem gcHhT_concave (D : GcHouseholdData U g q β) (hU : ConcaveOn ℝ (Ici 0) U)
    {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ} (hΩ : Continuous Ω) (hcv : GcConcaveA Ω) :
    GcConcaveA (gcHhT U g q β Ω) := by
  intro k x₁ x₂ x θ h0 h1 hx
  obtain ⟨b₁, hb₁, e₁⟩ := gcHhT_attained D hΩ (k, x₁)
  obtain ⟨b₂, hb₂, e₂⟩ := gcHhT_attained D hΩ (k, x₂)
  set b := gcAcombo b₁ b₂ h0 h1
  have hq := D.q_pos k
  have hθ' : 0 ≤ 1 - θ := by linarith
  have hb : q k * b ≤ x := by
    change q k * (θ * (b₁ : ℝ) + (1 - θ) * b₂) ≤ x
    rw [hx]
    change q k * b₁ ≤ x₁ at hb₁
    change q k * b₂ ≤ x₂ at hb₂
    nlinarith [mul_le_mul_of_nonneg_left hb₁ h0, mul_le_mul_of_nonneg_left hb₂ hθ']
  have hge := gcHhT_ge D hΩ (k, x) b hb
  have hcb := hcv (g k) b₁ b₂ b θ h0 h1 rfl
  have hUc := hU.2 (mem_Ici.2 (by linarith : (0 : ℝ) ≤ x₁ - q k * b₁))
    (mem_Ici.2 (by linarith : (0 : ℝ) ≤ x₂ - q k * b₂)) h0 hθ' (by ring)
  simp only [smul_eq_mul] at hUc
  have hcons : θ * ((x₁ : ℝ) - q k * b₁) + (1 - θ) * (x₂ - q k * b₂) = x - q k * b := by
    change _ = (x : ℝ) - q k * (θ * (b₁ : ℝ) + (1 - θ) * b₂)
    rw [hx]; ring
  rw [hcons] at hUc
  rw [e₁, e₂]
  change U ((x : ℝ) - q k * b) + β * Ω (g k, b) ≤ gcHhT U g q β Ω (k, x) at hge
  nlinarith [mul_le_mul_of_nonneg_left hcb D.beta_pos.le]

/-- The fixed point of `T` is concave in `a` when `U` is concave. -/
theorem gc_hh_fixed_concave (D : GcHouseholdData U g q β) (hU : ConcaveOn ℝ (Ici 0) U) :
    GcConcaveA ⇑(ContractingWith.fixedPoint (α := Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ) (gcHhTB D)
      (gc_hhTB_contracting D)) := by
  have hit : ∀ m, GcConcaveA ((gcHhTB D)^[m] 0) := by
    intro m
    induction m with
    | zero =>
      intro k x₁ x₂ x θ _ _ _
      simp
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact gcHhT_concave D hU (BoundedContinuousFunction.continuous _) ih
  have hlim := (gc_hhTB_contracting D).tendsto_iterate_fixedPoint 0
  intro k x₁ x₂ x θ h0 h1 hx
  have ev : ∀ p, Tendsto (fun n => (gcHhTB D)^[n] 0 p) atTop
      (𝓝 (ContractingWith.fixedPoint (α := Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ) (gcHhTB D)
        (gc_hhTB_contracting D) p)) := fun p =>
    ((continuous_eval_const p).tendsto _).comp hlim
  exact le_of_tendsto_of_tendsto' (((ev (k, x₁)).const_mul θ).add ((ev (k, x₂)).const_mul
    (1 - θ))) (ev (k, x)) fun n => hit n k x₁ x₂ x θ h0 h1 hx

/-- **The household's policy is single-valued**: with `U` strictly concave and `Ω(k′, ·)` concave,
the maximiser in (2) is unique. -/
theorem gc_hh_policy_unique (D : GcHouseholdData U g q β) (hU : StrictConcaveOn ℝ (Ici 0) U)
    {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ} (hΩ : GcHouseholdBellman U g q β Ω) (hcv : GcConcaveA Ω)
    (p : Icc a kmax × Ici (0 : ℝ)) {b₁ b₂ : Ici (0 : ℝ)} (hb₁ : q p.1 * b₁ ≤ p.2)
    (hb₂ : q p.1 * b₂ ≤ p.2) (e₁ : Ω p = U (p.2 - q p.1 * b₁) + β * Ω (g p.1, b₁))
    (e₂ : Ω p = U (p.2 - q p.1 * b₂) + β * Ω (g p.1, b₂)) : b₁ = b₂ := by
  by_contra hne
  have hq := D.q_pos p.1
  set b := gcAcombo b₁ b₂ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hb : q p.1 * b ≤ p.2 := by
    change q p.1 * (1 / 2 * (b₁ : ℝ) + (1 - 1 / 2) * b₂) ≤ p.2
    nlinarith
  have hge := (hΩ p).1 b hb
  have hcb := hcv (g p.1) b₁ b₂ b (1 / 2) (by norm_num) (by norm_num) rfl
  have hne' : (p.2 : ℝ) - q p.1 * b₁ ≠ p.2 - q p.1 * b₂ := fun h => hne (Subtype.ext (by
    have := mul_left_cancel₀ hq.ne' (by linarith : q p.1 * (b₁ : ℝ) = q p.1 * b₂)
    exact this))
  have hUs := hU.2 (mem_Ici.2 (by linarith : (0 : ℝ) ≤ p.2 - q p.1 * b₁))
    (mem_Ici.2 (by linarith : (0 : ℝ) ≤ p.2 - q p.1 * b₂)) hne' (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hUs
  have hcons : 1 / 2 * ((p.2 : ℝ) - q p.1 * b₁) + 1 / 2 * (p.2 - q p.1 * b₂) = p.2 - q p.1 * b := by
    change _ = (p.2 : ℝ) - q p.1 * (1 / 2 * (b₁ : ℝ) + (1 - 1 / 2) * b₂)
    ring
  rw [hcons] at hUs
  nlinarith [mul_le_mul_of_nonneg_left hcb D.beta_pos.le]

/-- The household's policy `ω(k, a)`: a maximiser in (2). -/
noncomputable def gcHhPolicy {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ}
    (hΩ : GcHouseholdBellman U g q β Ω) (p : Icc a kmax × Ici (0 : ℝ)) : Ici (0 : ℝ) :=
  Classical.choose (hΩ p).2

/-- The policy is feasible and attains (2). -/
theorem gcHhPolicy_spec {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ} (hΩ : GcHouseholdBellman U g q β Ω)
    (p : Icc a kmax × Ici (0 : ℝ)) :
    q p.1 * gcHhPolicy hΩ p ≤ p.2 ∧
      Ω p = U (p.2 - q p.1 * gcHhPolicy hΩ p) + β * Ω (g p.1, gcHhPolicy hΩ p) :=
  Classical.choose_spec (hΩ p).2

/-- **The household's policy is continuous** (Ex 16.1e). -/
theorem gc_hh_policy_continuous (D : GcHouseholdData U g q β) (hU : StrictConcaveOn ℝ (Ici 0) U)
    {Ω : Icc a kmax × Ici (0 : ℝ) → ℝ} (hΩc : Continuous Ω) (hΩ : GcHouseholdBellman U g q β Ω)
    (hcv : GcConcaveA Ω) : Continuous (gcHhPolicy hΩ) := by
  set pr : ℝ → Ici (0 : ℝ) := fun y => ⟨max 0 y, mem_Ici.2 (le_max_left _ _)⟩ with hpr
  have hprc : Continuous pr := Continuous.subtype_mk (continuous_const.max continuous_id) _
  set G : Icc a kmax × Ici (0 : ℝ) → ℝ → ℝ := fun p y =>
    U (max (p.2 - q p.1 * y) 0) + β * Ω (g p.1, pr y) with hG
  have hGc : Continuous fun r : (Icc a kmax × Ici (0 : ℝ)) × ℝ => G r.1 r.2 :=
    (D.continuous_Ue.comp ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).sub
      ((D.q_cont.comp (continuous_fst.comp continuous_fst)).mul continuous_snd))).add
      (continuous_const.mul (hΩc.comp ((D.g_cont.comp (continuous_fst.comp continuous_fst)).prodMk
        (hprc.comp continuous_snd))))
  have hb : Continuous fun p : Icc a kmax × Ici (0 : ℝ) => (p.2 : ℝ) / q p.1 :=
    (continuous_subtype_val.comp continuous_snd).div (D.q_cont.comp continuous_fst)
      fun p => (D.q_pos _).ne'
  have hb0 : ∀ p : Icc a kmax × Ici (0 : ℝ), 0 ≤ (p.2 : ℝ) / q p.1 := fun p =>
    div_nonneg p.2.2 (D.q_pos _).le
  have hfeas : ∀ p : Icc a kmax × Ici (0 : ℝ), ∀ y, y ∈ Icc 0 ((p.2 : ℝ) / q p.1) →
      q p.1 * y ≤ p.2 := fun p y hy => by
    have := hy.2
    rw [le_div_iff₀ (D.q_pos p.1)] at this
    linarith
  have hGeq : ∀ p : Icc a kmax × Ici (0 : ℝ), ∀ y, ∀ hy : y ∈ Icc 0 ((p.2 : ℝ) / q p.1),
      G p y = U (p.2 - q p.1 * (⟨y, hy.1⟩ : Ici (0 : ℝ))) + β * Ω (g p.1, ⟨y, hy.1⟩) := by
    intro p y hy
    have h1 : pr y = ⟨y, hy.1⟩ := Subtype.ext (max_eq_right hy.1)
    simp only [hG, h1, max_eq_left (by linarith [hfeas p y hy] : (0 : ℝ) ≤ p.2 - q p.1 * y)]
  have hmem : ∀ p, (gcHhPolicy hΩ p : ℝ) ∈ Icc 0 ((p.2 : ℝ) / q p.1) := fun p =>
    ⟨(gcHhPolicy hΩ p).2, by
      rw [le_div_iff₀ (D.q_pos p.1), mul_comm]
      exact (gcHhPolicy_spec hΩ p).1⟩
  have hGh : ∀ p, G p (gcHhPolicy hΩ p) = Ω p := fun p => by
    rw [hGeq p _ (hmem p)]
    exact (gcHhPolicy_spec hΩ p).2.symm
  have hcont := gc_argmax_continuous hb hb0 hGc (h := fun p => (gcHhPolicy hΩ p : ℝ)) hmem
    (fun p y hy => by
      rw [hGh, hGeq p y hy]
      exact (hΩ p).1 _ (hfeas p y hy))
    (fun p y hy hle => by
      rw [hGh, hGeq p y hy] at hle
      have e := le_antisymm ((hΩ p).1 ⟨y, hy.1⟩ (hfeas p y hy)) hle
      have := gc_hh_policy_unique D hU hΩ hcv p (b₁ := ⟨y, hy.1⟩) (hfeas p y hy)
        (gcHhPolicy_spec hΩ p).1 e.symm (gcHhPolicy_spec hΩ p).2
      exact congrArg Subtype.val this)
  exact Continuous.subtype_mk hcont _

/-- **Exercise 16.1(e), household**: there is exactly one bounded continuous `Ω` satisfying (2)
(unique even among bounded functions); `Ω(k, ·)` is concave; with `U` strictly concave the policy
`ω` is single-valued and continuous. -/
theorem ex_16_1e_household (D : GcHouseholdData U g q β) (hU : StrictConcaveOn ℝ (Ici 0) U) :
    ∃ Ω : Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ, ∃ hΩ : GcHouseholdBellman U g q β Ω,
      (∀ Ω' : Icc a kmax × Ici (0 : ℝ) → ℝ, (∃ C, ∀ p, |Ω' p| ≤ C) →
        GcHouseholdBellman U g q β Ω' → Ω' = Ω) ∧
      GcConcaveA Ω ∧ Continuous (gcHhPolicy hΩ) ∧
      ∀ p (a' : Ici (0 : ℝ)), q p.1 * a' ≤ p.2 →
        Ω p = U (p.2 - q p.1 * a') + β * Ω (g p.1, a') → a' = gcHhPolicy hΩ p := by
  set Ω := ContractingWith.fixedPoint (α := Icc a kmax × Ici (0 : ℝ) →ᵇ ℝ) (gcHhTB D)
    (gc_hhTB_contracting D)
  have hfix : gcHhTB D Ω = Ω := (gc_hhTB_contracting D).fixedPoint_isFixedPt
  have hΩ := gc_hhBellman_of_fixed D hfix
  have hcv := gc_hh_fixed_concave D hU.concaveOn
  refine ⟨Ω, hΩ, fun Ω' ⟨C, hC⟩ hΩ' => ?_, hcv,
    gc_hh_policy_continuous D hU Ω.continuous hΩ hcv, fun p a' ha' e => ?_⟩
  · refine gc_hhBellman_unique D hΩ' hΩ (C := C + ‖Ω‖) fun p => ?_
    have h2 : |Ω p| ≤ ‖Ω‖ := by
      rw [← Real.norm_eq_abs]
      exact Ω.norm_coe_le_norm p
    calc |Ω' p - Ω p| ≤ |Ω' p| + |Ω p| := abs_sub _ _
      _ ≤ C + ‖Ω‖ := add_le_add (hC p) h2
  · exact gc_hh_policy_unique D hU hΩ hcv p ha' (gcHhPolicy_spec hΩ p).1 e
      (gcHhPolicy_spec hΩ p).2

end StokeyLucasPrescott.EquilibriumApplications
