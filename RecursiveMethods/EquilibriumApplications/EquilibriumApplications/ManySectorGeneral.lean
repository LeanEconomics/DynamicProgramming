/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManySectorFeller
import EquilibriumApplications.ManySectorVerification

/-!
# Pricing securities with a general shock space (Ex 16.2(c), (d), (2), (g))

SLP §16.2, pp. 482–484. `ManySectorSecurities`, `ManySectorEnvelope` and
`ManySectorVerification` treat finitely many shocks, and `ManySectorFeller` a Feller transition on
a compact shock space with a continuous return. Here the state space `S` and the shock space `Z`
are arbitrary **measurable spaces** (no topology, no compactness: e.g. Polish or σ-compact shock
spaces, or any standard Borel space), the law of next period's shock is a **Markov kernel**
`Q : S → 𝒫(Z)`, and the return `R(s, z′) ≥ 0` and the next state `nxt(s, z′)` are merely jointly
measurable:

  (1) `w(A, s) = max {U(c(s) + A − q(s) b) + β ∫ w(b R(s, z′), nxt(s, z′)) Q(s, dz′) :
        b ≥ B, q(s) b ≤ c(s) + A}`.

For the book, `s = (x, z)`, `nxt(s, z′) = (g(x, z), z′)`, `R(s, z′) = f(z′)` with `f` bounded
measurable, and the kernel is `(x, z) ↦ Q(z, ·)` (the book's `Q` composed with the projection).

* `MsGenData`: the data (measurable `c`, `q > 0`, `R`, `nxt`; bounded continuous `U`; the domain
  condition `q(s′)B − c(s′) ≤ B R(s, z′)` of `ManySectorSecurities`); `msGE`, `msGObj`,
  `MsGBellman` (equation (1) on `D = msSecDom`, with "max").
* `msG_bellman_unique`: at most one solution of (1) among measurable functions bounded on `D`.
* The contraction: `MsGSpace = ℓ∞(S; C_b(ℝ))` (functions `w(A, s)` bounded, continuous in `A`)
  and its closed subset `msGMeas` (measurable in `s`), whose elements are jointly measurable
  Carathéodory functions (`msGFn_measurable`). The operator `msGTM` of (1) maps `msGMeas` to
  itself: continuity in `A` comes from dominated convergence in `b` (`msGE_continuous`), not from
  any continuity in `z′`; measurability in `s` from writing the max over `[0, 1]` as a supremum
  over the rationals (`msG_sSup_eq_iSup`, `msGT_measurable`) and the kernel's measurability.
  `msG_contracting`: Blackwell, modulus `β`.
* **Exercise 16.2(c), general shock space** (`ex_16_2c_general`): there is a bounded measurable
  `w`, continuous in `A`, satisfying (1) on `D`, and every measurable solution bounded on `D`
  agrees with it on `D`. `msG_exists` adds: concave in `A` when `U` is concave;
  `msG_solution_concave`: so is every measurable solution bounded on `D`.
* **Exercise 16.2(d), corrected** (`ex_16_2d_general`): `w₁(0, ŝ) = U′(c(ŝ) − q(ŝ) b*)`.
* `msGE_hasDerivAt`: differentiation under the integral sign, by dominated convergence (concavity
  traps the difference quotients between those at `±B`; no extra integrability needed);
  `msG_foc`: the first-order condition.
* **The pricing equation (2)** (`ex_16_2_eq2_general`) and **(3) for Exercise 16.2(g)**
  (`ex_16_2g_general`), with the finite sums replaced by integrals against `Q(s, ·)`.
* **Exercise 16.2(d), converse** (`ex_16_2d_converse_general`, via `msG_super_step`,
  `msG_supergradient`): (2) in every state makes no trade optimal; and
  `ex_16_2d_equilibrium_general`: in equilibrium `w₁(0, s) = U′(c(s))`.

**Hypotheses added.** As in the finite case: `q` given, the domain condition, `c > 0`, `U`
concave and differentiable on `(0, ∞)` with `U′ > 0` (for (d) and its converse), and
`U′(c(s))(c(s) − q(s)B)` bounded above (for the converse). New for the general case: `c`, `q`,
`R`, `nxt` measurable and `Q` a Markov kernel; uniqueness and (2)–(3) are for **measurable**
solutions bounded on `D` (for a non-measurable `w` the integral in (1) is meaningless); the
converse needs `z′ ↦ U′(c(s′)) R(s, z′)` to be `Q(s, ·)`-integrable (for (2) to make sense; it is
a consequence, not a hypothesis, in `ex_16_2_eq2_general`).

**Correction (NOTE (iii) to Ex 16.2c).** With a merely measurable return the solution of (1) need
not be continuous in the state; the right space is bounded functions measurable in `s` and
continuous in `A`, in which the contraction argument goes through without any continuity in `z′`.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BoundedContinuousFunction

variable {Sx : Type*} [MeasurableSpace Sx] {Z : Type*} [MeasurableSpace Z]

variable (U : ℝ → ℝ) (c q : Sx → ℝ) (R : Sx → Z → ℝ) (nxt : Sx → Z → Sx) in
/-- The data of (1) for a general measurable state space `S` and shock space `Z` (no topology):
`U` bounded continuous, `c`, `q` measurable with `q > 0`, the return `R(s, z′) ≥ 0` and the next
state `nxt(s, z′)` jointly measurable, and the domain condition `q(s′)B − c(s′) ≤ B R(s, z′)`.
The law of `z′` is a Markov kernel `Q`, given separately. -/
structure MsGenData (B β : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  B_neg : B < 0
  U_cont : Continuous U
  U_bdd : ∃ M, ∀ x, |U x| ≤ M
  c_meas : Measurable c
  q_meas : Measurable q
  q_pos : ∀ s, 0 < q s
  R_meas : Measurable fun p : Sx × Z => R p.1 p.2
  R_nonneg : ∀ s z', 0 ≤ R s z'
  nxt_meas : Measurable fun p : Sx × Z => nxt p.1 p.2
  dom : ∀ s z', q (nxt s z') * B - c (nxt s z') ≤ B * R s z'

/-- The expected continuation value `∫ w(b R(s, z′), nxt(s, z′)) Q(s, dz′)`. -/
noncomputable def msGE (R : Sx → Z → ℝ) (Q : Kernel Sx Z) (nxt : Sx → Z → Sx)
    (w : ℝ × Sx → ℝ) (s : Sx) (b : ℝ) : ℝ :=
  ∫ z', w (b * R s z', nxt s z') ∂(Q s)

/-- The objective of (1) at `(A, s)` for the purchase `b`. -/
noncomputable def msGObj (U : ℝ → ℝ) (c q : Sx → ℝ) (R : Sx → Z → ℝ) (Q : Kernel Sx Z)
    (nxt : Sx → Z → Sx) (β : ℝ) (w : ℝ × Sx → ℝ) (A : ℝ) (s : Sx) (b : ℝ) : ℝ :=
  U (c s + A - q s * b) + β * msGE R Q nxt w s b

/-- `w` **satisfies (1) on `D`** (with "max"), for a Markov kernel `Q`. -/
def MsGBellman (U : ℝ → ℝ) (c q : Sx → ℝ) (R : Sx → Z → ℝ) (Q : Kernel Sx Z)
    (nxt : Sx → Z → Sx) (B β : ℝ) (w : ℝ × Sx → ℝ) : Prop :=
  ∀ A s, q s * B - c s ≤ A →
    (∀ b, B ≤ b → q s * b ≤ c s + A → msGObj U c q R Q nxt β w A s b ≤ w (A, s)) ∧
    ∃ b, B ≤ b ∧ q s * b ≤ c s + A ∧ w (A, s) = msGObj U c q R Q nxt β w A s b

/-- The operator of (1): `(Tw)(A, s) = sup_{r ∈ [0, 1]}` of the objective at `b = msSecB A s r`. -/
noncomputable def msGT (U : ℝ → ℝ) (c q : Sx → ℝ) (R : Sx → Z → ℝ) (Q : Kernel Sx Z)
    (nxt : Sx → Z → Sx) (B β : ℝ) (w : ℝ × Sx → ℝ) (p : ℝ × Sx) : ℝ :=
  sSup ((fun r => msGObj U c q R Q nxt β w p.1 p.2 (msSecB c q B p.1 p.2 r)) '' Icc 0 1)

variable {U : ℝ → ℝ} {c q : Sx → ℝ} {R : Sx → Z → ℝ} {Q : Kernel Sx Z} {nxt : Sx → Z → Sx}
  {B β : ℝ}

/-- Feasible purchases lead to states in `D`. -/
theorem msG_next_mem (D : MsGenData U c q R nxt B β) (s : Sx) {b : ℝ} (hb : B ≤ b) (z' : Z) :
    (b * R s z', nxt s z') ∈ msSecDom c q B := by
  have h1 := D.dom s z'
  have h2 := D.R_nonneg s z'
  change q (nxt s z') * B - c (nxt s z') ≤ b * R s z'
  nlinarith

/-- `z′ ↦ (b R(s, z′), nxt(s, z′))` is measurable. -/
theorem msG_meas_next (D : MsGenData U c q R nxt B β) (s : Sx) (b : ℝ) :
    Measurable fun z' : Z => (b * R s z', nxt s z') :=
  (measurable_const.mul (D.R_meas.comp measurable_prodMk_left)).prodMk
    (D.nxt_meas.comp measurable_prodMk_left)

variable [IsMarkovKernel Q]

/-- For `w` measurable and bounded on `D`, the integrand of (1) is integrable (`b ≥ B`). -/
theorem msG_integrable (D : MsGenData U c q R nxt B β) {w : ℝ × Sx → ℝ} (hwm : Measurable w)
    {C : ℝ} (hC : ∀ p ∈ msSecDom c q B, |w p| ≤ C) (s : Sx) {b : ℝ} (hb : B ≤ b) :
    Integrable (fun z' => w (b * R s z', nxt s z')) (Q s) :=
  Integrable.of_bound (hwm.comp (msG_meas_next D s b)).aestronglyMeasurable C
    (Eventually.of_forall fun z' => by
      rw [Real.norm_eq_abs]; exact hC _ (msG_next_mem D s hb z'))

/-- `z′ ↦ w(0, nxt(s, z′))` is integrable. -/
theorem msG_integrable_zero (D : MsGenData U c q R nxt B β) {w : ℝ × Sx → ℝ}
    (hwm : Measurable w) {C : ℝ} (hC : ∀ p ∈ msSecDom c q B, |w p| ≤ C) (s : Sx) :
    Integrable (fun z' => w (0, nxt s z')) (Q s) := by
  simpa only [zero_mul] using msG_integrable (Q := Q) D hwm hC s D.B_neg.le

/-- `|∫ u − ∫ v| ≤ C` when `|u − v| ≤ C` pointwise. -/
theorem msG_sub_le {w w' : ℝ × Sx → ℝ} {s : Sx} {b : ℝ}
    (h1 : Integrable (fun z' => w (b * R s z', nxt s z')) (Q s))
    (h2 : Integrable (fun z' => w' (b * R s z', nxt s z')) (Q s)) {C : ℝ}
    (h : ∀ z', |w (b * R s z', nxt s z') - w' (b * R s z', nxt s z')| ≤ C) :
    |msGE R Q nxt w s b - msGE R Q nxt w' s b| ≤ C := by
  rw [msGE, msGE, ← integral_sub h1 h2]
  have := norm_integral_le_of_norm_le_const (μ := Q s)
    (f := fun z' => w (b * R s z', nxt s z') - w' (b * R s z', nxt s z')) (C := C)
    (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact h z')
  simpa [probReal_univ] using this

/-- **At most one solution of (1) among measurable functions bounded on `D`**. -/
theorem msG_bellman_unique (D : MsGenData U c q R nxt B β) {w w' : ℝ × Sx → ℝ}
    (hwm : Measurable w) (hw'm : Measurable w') {C C' : ℝ}
    (hC : ∀ p ∈ msSecDom c q B, |w p| ≤ C) (hC' : ∀ p ∈ msSecDom c q B, |w' p| ≤ C')
    (hw : MsGBellman U c q R Q nxt B β w) (hw' : MsGBellman U c q R Q nxt B β w') :
    ∀ p ∈ msSecDom c q B, w p = w' p := by
  have key : ∀ n, ∀ p ∈ msSecDom c q B, |w p - w' p| ≤ β ^ n * (C + C') := by
    intro n
    induction n with
    | zero =>
      intro p hp
      rw [pow_zero, one_mul]
      exact (abs_sub _ _).trans (add_le_add (hC p hp) (hC' p hp))
    | succ n ih =>
      rintro ⟨A, s⟩ hp
      obtain ⟨b₁, hb₁, hf₁, e₁⟩ := (hw A s hp).2
      obtain ⟨b₂, hb₂, hf₂, e₂⟩ := (hw' A s hp).2
      have a1 := (hw' A s hp).1 b₁ hb₁ hf₁
      have a2 := (hw A s hp).1 b₂ hb₂ hf₂
      have d1 := msG_sub_le (msG_integrable (Q := Q) D hwm hC s hb₁)
        (msG_integrable D hw'm hC' s hb₁) fun z' => ih _ (msG_next_mem D s hb₁ z')
      have d2 := msG_sub_le (msG_integrable (Q := Q) D hwm hC s hb₂)
        (msG_integrable D hw'm hC' s hb₂) fun z' => ih _ (msG_next_mem D s hb₂ z')
      simp only [msGObj] at e₁ e₂ a1 a2
      have hβ := D.beta_pos
      rw [pow_succ, mul_comm (β ^ n) β, mul_assoc]
      refine abs_le.2 ⟨?_, ?_⟩
      · nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 d2).1 hβ.le]
      · nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 d1).2 hβ.le]
  intro p hp
  have hlim : Tendsto (fun n : ℕ => β ^ n * (C + C')) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one D.beta_pos.le D.beta_lt_one).mul_const _
  have : |w p - w' p| ≤ 0 := ge_of_tendsto' hlim fun n => key n p hp
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-! ### Existence: a contraction on functions measurable in `s`, continuous in `A` -/

/-- The space `ℓ∞(S; C_b(ℝ))`: bounded families `s ↦ W(s) ∈ C_b(ℝ)`, read as
`w(A, s) = W(s)(A)` (bounded, continuous in `A`, no topology on `S`). -/
abbrev MsGSpace (Sx : Type*) : Type _ := lp (fun _ : Sx => ℝ →ᵇ ℝ) ⊤

/-- `W ∈ MsGSpace` read as a function of `(A, s)`. -/
def msGFn (W : MsGSpace Sx) (p : ℝ × Sx) : ℝ := W p.2 p.1

/-- The (closed) set of `W` with `s ↦ W(s)(A)` measurable for every `A`. -/
def msGMeas (Sx : Type*) [MeasurableSpace Sx] : Set (MsGSpace Sx) :=
  {W | ∀ A, Measurable fun s => W s A}

omit [MeasurableSpace Sx] in
/-- `|w(A, s)| ≤ ‖W‖`. -/
theorem msGFn_abs_le (W : MsGSpace Sx) (p : ℝ × Sx) : |msGFn W p| ≤ ‖W‖ := by
  rw [← Real.norm_eq_abs]
  exact ((W p.2).norm_coe_le_norm p.1).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero W p.2)

omit [MeasurableSpace Sx] in
/-- `|w(A, s) − w′(A, s)| ≤ ‖W − W′‖`. -/
theorem msGFn_sub_le (W W' : MsGSpace Sx) (p : ℝ × Sx) :
    |msGFn W p - msGFn W' p| ≤ ‖W - W'‖ := by
  rw [← Real.dist_eq]
  calc dist (W p.2 p.1) (W' p.2 p.1) ≤ dist (W p.2) (W' p.2) :=
        BoundedContinuousFunction.dist_coe_le_dist p.1
    _ = ‖(W - W') p.2‖ := by rw [dist_eq_norm, lp.coeFn_sub, Pi.sub_apply]
    _ ≤ ‖W - W'‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero _ p.2

/-- A `W ∈ msGMeas` gives a jointly measurable `w` (a Carathéodory function). -/
theorem msGFn_measurable {W : MsGSpace Sx} (hW : W ∈ msGMeas Sx) : Measurable (msGFn W) :=
  measurable_uncurry_of_continuous_of_measurable (u := fun A s => W s A)
    (fun s => (W s).continuous) hW

omit [MeasurableSpace Sx] in
/-- Evaluation `W ↦ W(s)(A)` is continuous. -/
theorem msG_continuous_eval (s : Sx) (A : ℝ) : Continuous fun W : MsGSpace Sx => W s A :=
  LipschitzWith.continuous (K := 1) <| LipschitzWith.of_dist_le_mul fun W W' => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
    exact msGFn_sub_le W W' (A, s)

/-- `msGMeas` is closed (pointwise limits of measurable functions are measurable). -/
theorem msGMeas_isClosed : IsClosed (msGMeas Sx) :=
  IsSeqClosed.isClosed fun _ W hmem hlim A =>
    measurable_of_tendsto_metrizable (fun n => hmem n A)
      (tendsto_pi_nhds.2 fun s => ((msG_continuous_eval s A).tendsto W).comp hlim)

/-- `0 ∈ msGMeas`. -/
theorem msG_zero_mem : (0 : MsGSpace Sx) ∈ msGMeas Sx := fun _ => by
  change Measurable fun _ : Sx => (0 : ℝ)
  exact measurable_const

/-- For `W ∈ msGMeas` the integrand of (1) is integrable for every `b`. -/
theorem msGFn_integrable (D : MsGenData U c q R nxt B β) {W : MsGSpace Sx}
    (hW : W ∈ msGMeas Sx) (s : Sx) (b : ℝ) :
    Integrable (fun z' => msGFn W (b * R s z', nxt s z')) (Q s) :=
  Integrable.of_bound ((msGFn_measurable hW).comp (msG_meas_next D s b)).aestronglyMeasurable ‖W‖
    (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact msGFn_abs_le W _)

/-- `b ↦ ∫ w(b R(s, z′), nxt(s, z′)) Q(s, dz′)` is continuous (dominated convergence; `w` is
continuous in `A`). -/
theorem msGE_continuous (D : MsGenData U c q R nxt B β) {W : MsGSpace Sx} (hW : W ∈ msGMeas Sx)
    (s : Sx) : Continuous fun b => msGE R Q nxt (msGFn W) s b :=
  continuous_of_dominated (bound := fun _ => ‖W‖)
    (fun b => ((msGFn_measurable hW).comp (msG_meas_next D s b)).aestronglyMeasurable)
    (fun b => Eventually.of_forall fun z' => by
      rw [Real.norm_eq_abs]; exact msGFn_abs_le W _)
    (integrable_const _)
    (Eventually.of_forall fun z' =>
      (W (nxt s z')).continuous.comp (continuous_id.mul continuous_const))

/-- The objective along `b = msSecB A s r` is jointly continuous in `(A, r)`. -/
theorem msGObj_continuous (D : MsGenData U c q R nxt B β) {W : MsGSpace Sx}
    (hW : W ∈ msGMeas Sx) (s : Sx) :
    Continuous fun p : ℝ × ℝ =>
      msGObj U c q R Q nxt β (msGFn W) p.1 s (msSecB c q B p.1 s p.2) := by
  have hb : Continuous fun p : ℝ × ℝ => msSecB c q B p.1 s p.2 :=
    continuous_const.add (continuous_snd.mul (continuous_const.max
      (((continuous_const.add continuous_fst).div_const _).sub continuous_const)))
  unfold msGObj
  exact (D.U_cont.comp ((continuous_const.add continuous_fst).sub (continuous_const.mul hb))).add
    (continuous_const.mul ((msGE_continuous D hW s).comp hb))

/-- The objective of (1) is bounded by `M + β ‖W‖`. -/
theorem msGObj_abs_le {M : ℝ} (hM : ∀ x, |U x| ≤ M) (hβ : 0 < β) (W : MsGSpace Sx) (A : ℝ)
    (s : Sx) (b : ℝ) : |msGObj U c q R Q nxt β (msGFn W) A s b| ≤ M + β * ‖W‖ := by
  have h0 : |msGE R Q nxt (msGFn W) s b| ≤ ‖W‖ := by
    have := norm_integral_le_of_norm_le_const (μ := Q s)
      (f := fun z' => msGFn W (b * R s z', nxt s z')) (C := ‖W‖)
      (Eventually.of_forall fun z' => by rw [Real.norm_eq_abs]; exact msGFn_abs_le W _)
    simpa [probReal_univ, msGE] using this
  unfold msGObj
  calc |U (c s + A - q s * b) + β * msGE R Q nxt (msGFn W) s b|
      ≤ |U (c s + A - q s * b)| + |β * msGE R Q nxt (msGFn W) s b| := abs_add_le _ _
    _ ≤ M + β * ‖W‖ := by
        rw [abs_mul, abs_of_pos hβ]
        exact add_le_add (hM _) (mul_le_mul_of_nonneg_left h0 hβ.le)

/-- The maximum defining `Tw` is attained. -/
theorem msGT_attained (D : MsGenData U c q R nxt B β) {W : MsGSpace Sx} (hW : W ∈ msGMeas Sx)
    (p : ℝ × Sx) : ∃ r ∈ Icc (0 : ℝ) 1, msGT U c q R Q nxt B β (msGFn W) p =
      msGObj U c q R Q nxt β (msGFn W) p.1 p.2 (msSecB c q B p.1 p.2 r) :=
  isCompact_Icc.exists_sSup_image_eq (nonempty_Icc.2 zero_le_one)
    ((msGObj_continuous D hW p.2).comp (continuous_const.prodMk continuous_id)).continuousOn

/-- `Tw` dominates the objective at every `r ∈ [0, 1]`. -/
theorem msGT_ge (D : MsGenData U c q R nxt B β) {W : MsGSpace Sx} (hW : W ∈ msGMeas Sx)
    (p : ℝ × Sx) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    msGObj U c q R Q nxt β (msGFn W) p.1 p.2 (msSecB c q B p.1 p.2 r) ≤
      msGT U c q R Q nxt B β (msGFn W) p :=
  le_csSup (isCompact_Icc.image ((msGObj_continuous D hW p.2).comp
    (continuous_const.prodMk continuous_id))).bddAbove (mem_image_of_mem _ hr)

/-- `A ↦ (Tw)(A, s)` is continuous. -/
theorem msGT_continuous (D : MsGenData U c q R nxt B β) {W : MsGSpace Sx}
    (hW : W ∈ msGMeas Sx) (s : Sx) :
    Continuous fun A => msGT U c q R Q nxt B β (msGFn W) (A, s) :=
  isCompact_Icc.continuous_sSup (f := fun A r =>
    msGObj U c q R Q nxt β (msGFn W) A s (msSecB c q B A s r)) (msGObj_continuous D hW s)

/-- For continuous `G`, `max_{[0, 1]} G = sup_{r ∈ ℚ ∩ (0, 1)} G(r)` (a countable supremum). -/
theorem msG_sSup_eq_iSup {G : ℝ → ℝ} (hG : Continuous G) :
    sSup (G '' Icc 0 1) = ⨆ r : {r : ℚ // (r : ℝ) ∈ Ioo (0 : ℝ) 1}, G r := by
  have hne : Nonempty {r : ℚ // (r : ℝ) ∈ Ioo (0 : ℝ) 1} := ⟨⟨1 / 2, by norm_num⟩⟩
  have hbdd : BddAbove (G '' Icc 0 1) := (isCompact_Icc.image hG).bddAbove
  have hbddT : BddAbove (range fun r : {r : ℚ // (r : ℝ) ∈ Ioo (0 : ℝ) 1} => G r) :=
    hbdd.mono (by
      rintro _ ⟨r, rfl⟩
      exact mem_image_of_mem G (Ioo_subset_Icc_self r.2))
  refine le_antisymm (csSup_le ((nonempty_Icc.2 zero_le_one).image G) ?_)
    (ciSup_le fun r => le_csSup hbdd (mem_image_of_mem G (Ioo_subset_Icc_self r.2)))
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ closure (Ioo (0 : ℝ) 1 ∩ range ((↑) : ℚ → ℝ)) := by
    have h1 := Dense.open_subset_closure_inter (Rat.denseRange_cast (𝕜 := ℝ))
      (isOpen_Ioo (a := (0 : ℝ)) (b := 1))
    rw [← closure_Ioo (zero_ne_one' ℝ)] at hx
    exact closure_minimal h1 isClosed_closure hx
  have h2 := image_closure_subset_closure_image hG (mem_image_of_mem G hx')
  have h3 : G '' (Ioo (0 : ℝ) 1 ∩ range ((↑) : ℚ → ℝ)) ⊆
      Iic (⨆ r : {r : ℚ // (r : ℝ) ∈ Ioo (0 : ℝ) 1}, G r) := by
    rintro _ ⟨y, ⟨hy, ⟨r, rfl⟩⟩, rfl⟩
    exact le_ciSup hbddT (⟨r, hy⟩ : {r : ℚ // (r : ℝ) ∈ Ioo (0 : ℝ) 1})
  exact closure_minimal h3 isClosed_Iic h2

/-- `s ↦ (Tw)(A, s)` is measurable (a countable supremum of measurable functions; the
expectation is measurable in `s` because `Q` is a kernel). -/
theorem msGT_measurable (D : MsGenData U c q R nxt B β) {W : MsGSpace Sx}
    (hW : W ∈ msGMeas Sx) (A : ℝ) :
    Measurable fun s => msGT U c q R Q nxt B β (msGFn W) (A, s) := by
  have heq : (fun s => msGT U c q R Q nxt B β (msGFn W) (A, s)) = fun s =>
      ⨆ r : {r : ℚ // (r : ℝ) ∈ Ioo (0 : ℝ) 1},
        msGObj U c q R Q nxt β (msGFn W) A s (msSecB c q B A s r) := by
    funext s
    exact msG_sSup_eq_iSup (G := fun r => msGObj U c q R Q nxt β (msGFn W) A s
      (msSecB c q B A s r)) ((msGObj_continuous D hW s).comp
        (continuous_const.prodMk continuous_id))
  rw [heq]
  refine Measurable.iSup fun r => ?_
  have hb : Measurable fun s => msSecB c q B A s r :=
    measurable_const.add (measurable_const.mul (measurable_const.max
      (((D.c_meas.add_const A).div D.q_meas).sub_const B)))
  unfold msGObj
  refine (D.U_cont.measurable.comp ((D.c_meas.add_const A).sub (D.q_meas.mul hb))).add
    (measurable_const.mul ?_)
  have hf : Measurable fun p : Sx × Z => msGFn W (msSecB c q B A p.1 r * R p.1 p.2, nxt p.1 p.2) :=
    (msGFn_measurable hW).comp (((hb.comp measurable_fst).mul D.R_meas).prodMk D.nxt_meas)
  exact (hf.stronglyMeasurable.integral_kernel_prod_right' (κ := Q)).measurable

/-- `0 ≤ M` when `|U| ≤ M`. -/
theorem msG_bound_nonneg (D : MsGenData U c q R nxt B β) (W : MsGSpace Sx) :
    0 ≤ Classical.choose D.U_bdd + β * ‖W‖ :=
  add_nonneg ((abs_nonneg _).trans (Classical.choose_spec D.U_bdd 0))
    (mul_nonneg D.beta_pos.le (norm_nonneg _))

variable (Q) in
/-- The operator of (1) on `msGMeas`: `(TW)(s)(A) = (Tw)(A, s)`. -/
noncomputable def msGTW (D : MsGenData U c q R nxt B β) (W : msGMeas Sx) : MsGSpace Sx :=
  ⟨fun s => BoundedContinuousFunction.ofNormedAddCommGroup
      (fun A => msGT U c q R Q nxt B β (msGFn W.1) (A, s)) (msGT_continuous D W.2 s)
      (Classical.choose D.U_bdd + β * ‖W.1‖) (fun A => by
        rw [Real.norm_eq_abs]
        obtain ⟨r, -, e⟩ := msGT_attained (Q := Q) D W.2 (A, s)
        rw [e]
        exact msGObj_abs_le (Classical.choose_spec D.U_bdd) D.beta_pos W.1 _ _ _),
    memℓp_infty ⟨Classical.choose D.U_bdd + β * ‖W.1‖, by
      rintro _ ⟨s, rfl⟩
      exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (msG_bound_nonneg D W.1) _⟩⟩

/-- Values of `msGTW`. -/
theorem msGTW_apply (D : MsGenData U c q R nxt B β) (W : msGMeas Sx) (s : Sx) (A : ℝ) :
    msGTW Q D W s A = msGT U c q R Q nxt B β (msGFn W.1) (A, s) := rfl

variable (Q) in
/-- The operator of (1) as a self-map of `msGMeas`. -/
noncomputable def msGTM (D : MsGenData U c q R nxt B β) (W : msGMeas Sx) : msGMeas Sx :=
  ⟨msGTW Q D W, fun A => msGT_measurable D W.2 A⟩

/-- **Blackwell**: the operator of (1) is a contraction of modulus `β` on `msGMeas`. -/
theorem msG_contracting (D : MsGenData U c q R nxt B β) :
    ContractingWith ⟨β, D.beta_pos.le⟩ (msGTM Q D) := by
  refine ⟨D.beta_lt_one, LipschitzWith.of_dist_le_mul fun W W' => ?_⟩
  change dist (msGTW Q D W) (msGTW Q D W') ≤ β * dist W.1 W'.1
  rw [dist_eq_norm, dist_eq_norm]
  refine lp.norm_le_of_forall_le (mul_nonneg D.beta_pos.le (norm_nonneg _)) fun s => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, ← dist_eq_norm]
  refine (BoundedContinuousFunction.dist_le (mul_nonneg D.beta_pos.le (norm_nonneg _))).2
    fun A => ?_
  rw [Real.dist_eq, msGTW_apply, msGTW_apply]
  obtain ⟨r₁, hr₁, e₁⟩ := msGT_attained (Q := Q) D W.2 (A, s)
  obtain ⟨r₂, hr₂, e₂⟩ := msGT_attained (Q := Q) D W'.2 (A, s)
  have a1 := msGT_ge (Q := Q) D W'.2 (A, s) hr₁
  have a2 := msGT_ge (Q := Q) D W.2 (A, s) hr₂
  have hd : ∀ b, |msGE R Q nxt (msGFn W.1) s b - msGE R Q nxt (msGFn W'.1) s b| ≤
      ‖W.1 - W'.1‖ := fun b =>
    msG_sub_le (msGFn_integrable D W.2 s b) (msGFn_integrable D W'.2 s b)
      fun z' => msGFn_sub_le W.1 W'.1 _
  have d1 := hd (msSecB c q B A s r₁)
  have d2 := hd (msSecB c q B A s r₂)
  simp only [msGObj] at e₁ e₂ a1 a2
  have hβ := D.beta_pos
  refine abs_le.2 ⟨?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 d2).1 hβ.le]
  · nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 d1).2 hβ.le]

/-- A fixed point of the operator satisfies (1) on `D`. -/
theorem msG_bellman_of_fixed (D : MsGenData U c q R nxt B β) {W : msGMeas Sx}
    (hfix : msGTM Q D W = W) : MsGBellman U c q R Q nxt B β (msGFn W.1) := by
  intro A s hp
  have hwp : msGFn W.1 (A, s) = msGT U c q R Q nxt B β (msGFn W.1) (A, s) :=
    (congrArg (fun V : msGMeas Sx => V.1 s A) hfix).symm
  refine ⟨fun b hb hf => ?_, ?_⟩
  · obtain ⟨r, hr, hrb⟩ := msFB_surj D.q_pos hp hb hf
    have := msGT_ge (Q := Q) D W.2 (A, s) hr
    rw [hrb] at this
    rw [hwp]
    exact this
  · obtain ⟨r, hr, e⟩ := msGT_attained (Q := Q) D W.2 (A, s)
    obtain ⟨h1, h2⟩ := msFB_feasible D.q_pos hp hr
    exact ⟨_, h1, h2, hwp.trans e⟩

/-- The operator of (1) preserves concavity in `A` (on the slices of `D`) when `U` is concave. -/
theorem msGT_concave (D : MsGenData U c q R nxt B β) (hU : ConcaveOn ℝ (Ici 0) U)
    {W : MsGSpace Sx} (hW : W ∈ msGMeas Sx) (hcv : MsSecConcave c q B (msGFn W)) :
    MsSecConcave c q B (msGT U c q R Q nxt B β (msGFn W)) := by
  intro s A₁ A₂ θ h1 h2 h0 hθ
  have hθ' : 0 ≤ 1 - θ := by linarith
  have hq := D.q_pos s
  obtain ⟨r₁, hr₁, e₁⟩ := msGT_attained (Q := Q) D hW (A₁, s)
  obtain ⟨r₂, hr₂, e₂⟩ := msGT_attained (Q := Q) D hW (A₂, s)
  set b₁ := msSecB c q B A₁ s r₁
  set b₂ := msSecB c q B A₂ s r₂
  obtain ⟨f₁, g₁⟩ := msFB_feasible D.q_pos h1 hr₁
  obtain ⟨f₂, g₂⟩ := msFB_feasible D.q_pos h2 hr₂
  set A := θ * A₁ + (1 - θ) * A₂
  set b := θ * b₁ + (1 - θ) * b₂
  have hA : q s * B - c s ≤ A := by nlinarith
  have hbB : B ≤ b := by nlinarith
  have hbf : q s * b ≤ c s + A := by
    simp only [b, A]
    nlinarith [mul_le_mul_of_nonneg_left g₁ h0, mul_le_mul_of_nonneg_left g₂ hθ']
  obtain ⟨r, hr, hrb⟩ := msFB_surj D.q_pos hA hbB hbf
  have hge := msGT_ge (Q := Q) D hW (A, s) hr
  rw [hrb] at hge
  have hUc := hU.2 (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c s + A₁ - q s * b₁))
    (mem_Ici.2 (by linarith : (0 : ℝ) ≤ c s + A₂ - q s * b₂)) h0 hθ' (by ring)
  simp only [smul_eq_mul] at hUc
  have hcons : θ * (c s + A₁ - q s * b₁) + (1 - θ) * (c s + A₂ - q s * b₂) =
      c s + A - q s * b := by simp only [b, A]; ring
  rw [hcons] at hUc
  have i1 := msGFn_integrable (Q := Q) D hW s b₁
  have i2 := msGFn_integrable (Q := Q) D hW s b₂
  have i3 := msGFn_integrable (Q := Q) D hW s b
  have hsum : θ * msGE R Q nxt (msGFn W) s b₁ + (1 - θ) * msGE R Q nxt (msGFn W) s b₂ ≤
      msGE R Q nxt (msGFn W) s b := by
    unfold msGE
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (i1.const_mul θ) (i2.const_mul (1 - θ))]
    refine integral_mono ((i1.const_mul θ).add (i2.const_mul (1 - θ))) i3 fun z' => ?_
    have hc := hcv (nxt s z') (b₁ * R s z') (b₂ * R s z') θ (msG_next_mem D s f₁ z')
      (msG_next_mem D s f₂ z') h0 hθ
    have e : θ * (b₁ * R s z') + (1 - θ) * (b₂ * R s z') = b * R s z' := by simp only [b]; ring
    rw [e] at hc
    exact hc
  rw [e₁, e₂]
  simp only [msGObj] at hge ⊢
  nlinarith [mul_le_mul_of_nonneg_left hsum D.beta_pos.le]

variable (Q) in
/-- **Existence for (1)**: the fixed point of the operator is a measurable, bounded solution of
(1) on `D`, continuous in `A`, and concave in `A` on the slices of `D` when `U` is concave. -/
theorem msG_exists (D : MsGenData U c q R nxt B β) :
    ∃ w : ℝ × Sx → ℝ, Measurable w ∧ (∃ C, ∀ p, |w p| ≤ C) ∧
      (∀ s, Continuous fun A => w (A, s)) ∧ MsGBellman U c q R Q nxt B β w ∧
      (ConcaveOn ℝ (Ici 0) U → MsSecConcave c q B w) := by
  have : CompleteSpace (msGMeas Sx) := msGMeas_isClosed.isComplete.completeSpace_coe
  have : Nonempty (msGMeas Sx) := ⟨⟨0, msG_zero_mem⟩⟩
  set W := ContractingWith.fixedPoint (msGTM Q D) (msG_contracting D)
  have hfix : msGTM Q D W = W := (msG_contracting D).fixedPoint_isFixedPt
  refine ⟨msGFn W.1, msGFn_measurable W.2, ⟨_, msGFn_abs_le W.1⟩, fun s => (W.1 s).continuous,
    msG_bellman_of_fixed D hfix, fun hU => ?_⟩
  set W₀ : msGMeas Sx := ⟨0, msG_zero_mem⟩
  have hit : ∀ m, MsSecConcave c q B (msGFn ((msGTM Q D)^[m] W₀).1) := by
    intro m
    induction m with
    | zero =>
      intro s A₁ A₂ θ _ _ _ _
      change θ * 0 + (1 - θ) * 0 ≤ 0
      simp
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact msGT_concave D hU ((msGTM Q D)^[m] W₀).2 ih
  have hlim := (msG_contracting (Q := Q) D).tendsto_iterate_fixedPoint W₀
  have ev : ∀ p : ℝ × Sx, Tendsto (fun n => msGFn ((msGTM Q D)^[n] W₀).1 p) atTop
      (𝓝 (msGFn W.1 p)) := fun p =>
    (((msG_continuous_eval p.2 p.1).comp continuous_subtype_val).tendsto _).comp hlim
  intro s A₁ A₂ θ h1 h2 h0 hθ
  exact le_of_tendsto_of_tendsto' (((ev (A₁, s)).const_mul θ).add ((ev (A₂, s)).const_mul
    (1 - θ))) (ev _) fun n => hit n s A₁ A₂ θ h1 h2 h0 hθ

variable (Q) in
/-- **Exercise 16.2(c) for a general shock space** (given `q`, with the domain condition): for a
Markov kernel `Q` on a measurable shock space and a measurable return, there is a bounded
measurable `w`, continuous in `A`, satisfying (1) on `D`; every measurable solution of (1) that is
bounded on `D` agrees with it on `D`. -/
theorem ex_16_2c_general (D : MsGenData U c q R nxt B β) :
    ∃ w : ℝ × Sx → ℝ, Measurable w ∧ (∃ C, ∀ p, |w p| ≤ C) ∧
      (∀ s, Continuous fun A => w (A, s)) ∧ MsGBellman U c q R Q nxt B β w ∧
      ∀ w' : ℝ × Sx → ℝ, Measurable w' → (∃ C, ∀ p ∈ msSecDom c q B, |w' p| ≤ C) →
        MsGBellman U c q R Q nxt B β w' → ∀ p ∈ msSecDom c q B, w' p = w p := by
  obtain ⟨w, hwm, ⟨C, hC⟩, hcont, hw, -⟩ := msG_exists Q D
  exact ⟨w, hwm, ⟨C, hC⟩, hcont, hw, fun w' hw'm ⟨C', hC'⟩ hw' =>
    msG_bellman_unique (Q := Q) D hw'm hwm hC' (fun p _ => hC p) hw' hw⟩

/-- **Every measurable solution of (1) bounded on `D` is concave in `A`** (on the slices of `D`)
when `U` is concave: it agrees on `D` with the concave fixed point. -/
theorem msG_solution_concave (D : MsGenData U c q R nxt B β) (hU : ConcaveOn ℝ (Ici 0) U)
    {w : ℝ × Sx → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ p ∈ msSecDom c q B, |w p| ≤ C)
    (hw : MsGBellman U c q R Q nxt B β w) : MsSecConcave c q B w := by
  obtain ⟨w₀, hwm₀, ⟨C₀, hC₀⟩, -, hw₀, hcv⟩ := msG_exists Q D
  have heq := msG_bellman_unique D hwm hwm₀ hC (fun p _ => hC₀ p) hw hw₀
  intro s A₁ A₂ θ h1 h2 h0 hθ
  have h3 : q s * B - c s ≤ θ * A₁ + (1 - θ) * A₂ := by nlinarith
  rw [heq (A₁, s) h1, heq (A₂, s) h2, heq (θ * A₁ + (1 - θ) * A₂, s) h3]
  exact hcv hU s A₁ A₂ θ h1 h2 h0 hθ

/-! ### Exercise 16.2(d), the pricing equations (2) and (3) -/

omit [IsMarkovKernel Q] in
/-- **Exercise 16.2(d), corrected, general shock space**: let `w` satisfy (1) and be concave in
`A`. If `b*` is optimal at `(0, ŝ)` and consumption `c(ŝ) − q(ŝ) b*` is positive, then `w(·, ŝ)` is
differentiable at `0` with `w₁(0, ŝ) = U′(c(ŝ) − q(ŝ) b*)`. -/
theorem ex_16_2d_general (D : MsGenData U c q R nxt B β) {dU : ℝ → ℝ}
    (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) {w : ℝ × Sx → ℝ}
    (hw : MsGBellman U c q R Q nxt B β w) (hcv : MsSecConcave c q B w) {s : Sx}
    {b : ℝ} (hb : B ≤ b) (hopt : w (0, s) = msGObj U c q R Q nxt β w 0 s b)
    (hcons : 0 < c s - q s * b) :
    HasDerivAt (fun A => w (A, s)) (dU (c s - q s * b)) 0 := by
  have hq := D.q_pos s
  have hm1 : 0 < c s - q s * B := by nlinarith [D.B_neg]
  set r := min (c s - q s * B) (c s - q s * b) with hr
  have hr0 : 0 < r := lt_min hm1 hcons
  have hsl : ∀ A ∈ Ioo (-r) r, q s * B - c s ≤ A := fun A hA => by
    linarith [hA.1, min_le_left (c s - q s * B) (c s - q s * b)]
  have hfe : ∀ A ∈ Ioo (-r) r, q s * b ≤ c s + A := fun A hA => by
    linarith [hA.1, min_le_right (c s - q s * B) (c s - q s * b)]
  set L : ℝ → ℝ := fun A => msGObj U c q R Q nxt β w A s b with hL
  have hcvW : ConcaveOn ℝ (Ioo (-r) r) fun A => w (A, s) := by
    refine ⟨convex_Ioo _ _, fun x hx y hy a a' ha ha' haa => ?_⟩
    obtain rfl : a' = 1 - a := by linarith
    simpa only [smul_eq_mul] using hcv s x y a (hsl x hx) (hsl y hy) ha (by linarith)
  have hLd : HasDerivAt L (dU (c s - q s * b)) 0 := by
    have hin : HasDerivAt (fun A : ℝ => c s + A - q s * b) 1 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_add (c s)).sub_const _
    have hU' : HasDerivAt U (dU (c s - q s * b)) (c s + 0 - q s * b) := by
      rw [add_zero]; exact hdU _ hcons
    have := (hU'.comp (0 : ℝ) hin).add_const (β * msGE R Q nxt w s b)
    simpa [hL, msGObj, Function.comp_def] using this
  exact ms_bs_envelope hr0 hcvW (fun A hA => (hw A s (hsl A hA)).1 b hb (hfe A hA))
    (by exact hopt.symm) hLd

/-- **Differentiation under the integral**: if `w` is measurable, bounded on `D`, concave in `A`
and each `w(·, nxt(s, z′))` has derivative `Dw(z′)` at `0`, then
`b ↦ ∫ w(b R(s, z′), nxt(s, z′)) Q(s, dz′)` has derivative `∫ Dw(z′) R(s, z′) Q(s, dz′)` at `0`.
(Dominated convergence: by concavity, for `0 < |h| ≤ −B` the difference quotient in `h` lies
between those at `−B` and at `B`.) -/
theorem msGE_hasDerivAt (D : MsGenData U c q R nxt B β) {w : ℝ × Sx → ℝ} (hwm : Measurable w)
    {C : ℝ} (hC : ∀ p ∈ msSecDom c q B, |w p| ≤ C) (hcv : MsSecConcave c q B w) (s : Sx)
    {Dw : Z → ℝ} (hD : ∀ z', HasDerivAt (fun A => w (A, nxt s z')) (Dw z') 0) :
    HasDerivAt (msGE R Q nxt w s) (∫ z', Dw z' * R s z' ∂(Q s)) 0 := by
  have hB := D.B_neg
  have hconc : ∀ z', ConcaveOn ℝ (Ici B) fun b => w (b * R s z', nxt s z') := fun z' => by
    refine ⟨convex_Ici B, fun x hx y hy a a' ha ha' haa => ?_⟩
    obtain rfl : a' = 1 - a := by linarith
    have h := hcv (nxt s z') (x * R s z') (y * R s z') a (msG_next_mem D s hx z')
      (msG_next_mem D s hy z') ha (by linarith)
    have e : a * (x * R s z') + (1 - a) * (y * R s z') = (a • x + (1 - a) • y) * R s z' := by
      simp only [smul_eq_mul]; ring
    rw [e] at h
    simpa only [smul_eq_mul] using h
  have hslope : ∀ z' h, h ∈ Icc B (-B) → h ≠ 0 →
      slope (fun b => w (b * R s z', nxt s z')) 0 (-B) ≤
          slope (fun b => w (b * R s z', nxt s z')) 0 h ∧
        slope (fun b => w (b * R s z', nxt s z')) 0 h ≤
          slope (fun b => w (b * R s z', nxt s z')) 0 B := by
    intro z' h hh h0
    have hcvx := (hconc z').neg
    have m0 : (0 : ℝ) ∈ Ici B := mem_Ici.2 hB.le
    have mB : B ∈ Ici B := mem_Ici.2 le_rfl
    have mh : h ∈ Ici B := mem_Ici.2 hh.1
    have mnB : -B ∈ Ici B := mem_Ici.2 (by linarith)
    have s1 := hcvx.secant_mono m0 mB mh hB.ne h0 hh.1
    have s2 := hcvx.secant_mono m0 mh mnB h0 (by linarith : -B ≠ 0) hh.2
    have k1 : ∀ x : ℝ, ((-fun b => w (b * R s z', nxt s z')) x -
        (-fun b => w (b * R s z', nxt s z')) 0) / (x - 0) =
        -slope (fun b => w (b * R s z', nxt s z')) 0 x := fun x => by
      rw [slope_def_field, Pi.neg_apply, Pi.neg_apply]; ring
    rw [k1, k1] at s1 s2
    exact ⟨by linarith, by linarith⟩
  have hint : ∀ b, B ≤ b → Integrable (fun z' => w (b * R s z', nxt s z')) (Q s) :=
    fun b hb => msG_integrable D hwm hC s hb
  have hslI : ∀ b, B ≤ b →
      Integrable (fun z' => slope (fun b => w (b * R s z', nxt s z')) 0 b) (Q s) := by
    intro b hb
    simp only [slope, vsub_eq_sub, smul_eq_mul]
    exact ((hint b hb).sub (hint 0 hB.le)).const_mul _
  have hslopeInt : ∀ h, B ≤ h →
      ∫ z', slope (fun b => w (b * R s z', nxt s z')) 0 h ∂(Q s) =
        slope (msGE R Q nxt w s) 0 h := by
    intro h hh
    simp only [slope, vsub_eq_sub, smul_eq_mul, msGE]
    rw [integral_const_mul, integral_sub (hint h hh) (hint 0 hB.le)]
  have hφd : ∀ z', HasDerivAt (fun b => w (b * R s z', nxt s z')) (Dw z' * R s z') 0 := by
    intro z'
    have hinner : HasDerivAt (fun b : ℝ => b * R s z') (R s z') 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const (R s z')
    have hD' : HasDerivAt (fun A => w (A, nxt s z')) (Dw z') (0 * R s z') := by
      rw [zero_mul]; exact hD z'
    exact hD'.comp (0 : ℝ) hinner
  rw [hasDerivAt_iff_tendsto_slope]
  have hev : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ∈ Ioo B (-B) ∧ h ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds hB (by linarith : (0 : ℝ) < -B)),
      self_mem_nhdsWithin] with h h1 h2
    exact ⟨h1, h2⟩
  have hlim : Tendsto (fun h => ∫ z', slope (fun b => w (b * R s z', nxt s z')) 0 h ∂(Q s))
      (𝓝[≠] 0) (𝓝 (∫ z', Dw z' * R s z' ∂(Q s))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun z' => |slope (fun b => w (b * R s z', nxt s z')) 0 B| +
        |slope (fun b => w (b * R s z', nxt s z')) 0 (-B)|) ?_ ?_
      ((hslI B le_rfl).abs.add (hslI (-B) (by linarith)).abs)
      (Eventually.of_forall fun z' => hasDerivAt_iff_tendsto_slope.1 (hφd z'))
    · refine Eventually.of_forall fun h => ?_
      simp only [slope, vsub_eq_sub, smul_eq_mul]
      exact (((hwm.comp (msG_meas_next D s h)).sub
        (hwm.comp (msG_meas_next D s 0))).const_mul _).aestronglyMeasurable
    · filter_upwards [hev] with h hh
      refine Eventually.of_forall fun z' => ?_
      obtain ⟨l1, l2⟩ := hslope z' h (Ioo_subset_Icc_self hh.1) hh.2
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [neg_abs_le (slope (fun b => w (b * R s z', nxt s z')) 0 (-B)),
          abs_nonneg (slope (fun b => w (b * R s z', nxt s z')) 0 B)]
      · linarith [le_abs_self (slope (fun b => w (b * R s z', nxt s z')) 0 B),
          abs_nonneg (slope (fun b => w (b * R s z', nxt s z')) 0 (-B))]
  refine hlim.congr' ?_
  filter_upwards [hev] with h hh
  exact hslopeInt h hh.1.1.le

/-- **The first-order condition for (1)**, general shock space: if `b = 0` is optimal at `(0, s)`
with `c(s) > 0`, `w` is measurable, bounded on `D` and concave in `A`, and each `w(·, s′)` has
derivative `Dw(z′)` at `0`, then `q(s) U′(c(s)) = β ∫ Dw(z′) R(s, z′) Q(s, dz′)`. -/
theorem msG_foc (D : MsGenData U c q R nxt B β) {dU : ℝ → ℝ}
    (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) {w : ℝ × Sx → ℝ} (hwm : Measurable w) {C : ℝ}
    (hC : ∀ p ∈ msSecDom c q B, |w p| ≤ C) (hw : MsGBellman U c q R Q nxt B β w)
    (hcv : MsSecConcave c q B w) {s : Sx} (hc : 0 < c s)
    (hopt : w (0, s) = msGObj U c q R Q nxt β w 0 s 0) {Dw : Z → ℝ}
    (hD : ∀ z', HasDerivAt (fun A => w (A, nxt s z')) (Dw z') 0) :
    q s * dU (c s) = β * ∫ z', Dw z' * R s z' ∂(Q s) := by
  have hq := D.q_pos s
  have hdom : q s * B - c s ≤ 0 := by nlinarith [D.B_neg]
  set Ψ : ℝ → ℝ := fun b => msGObj U c q R Q nxt β w 0 s b with hΨ
  have hmax : IsLocalMax Ψ 0 := by
    have h1 : ∀ᶠ b in 𝓝 (0 : ℝ), B < b := (tendsto_id).eventually_const_lt D.B_neg
    have h2 : ∀ᶠ b in 𝓝 (0 : ℝ), q s * b < c s + 0 := by
      have : Tendsto (fun b : ℝ => q s * b) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (q s)
      exact this.eventually_lt_const (by linarith)
    filter_upwards [h1, h2] with b hb1 hb2
    have := (hw 0 s hdom).1 b hb1.le hb2.le
    simp only [hΨ]
    rw [← hopt]
    exact this
  have hin : HasDerivAt (fun b : ℝ => c s + 0 - q s * b) (-(q s)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (q s)).const_sub (c s + 0)
  have hU' : HasDerivAt U (dU (c s)) (c s + 0 - q s * 0) := by
    simp only [add_zero, mul_zero, sub_zero]; exact hdU _ hc
  have hE := msGE_hasDerivAt D hwm hC hcv s (Q := Q) hD
  have hΨd : HasDerivAt Ψ (dU (c s) * -(q s) + β * ∫ z', Dw z' * R s z' ∂(Q s)) 0 := by
    have hΨeq : Ψ = (fun b => U (c s + 0 - q s * b)) + fun b => β * msGE R Q nxt w s b := by
      funext b; rfl
    rw [hΨeq]
    exact (hU'.comp (0 : ℝ) hin).add (hE.const_mul β)
  have := hmax.hasDerivAt_eq_zero hΨd
  linarith

/-- **The pricing equation (2)**, general shock space: if `c > 0`, `w` is a measurable solution of
(1) bounded on `D` and concave in `A`, and `b = 0` is optimal at `A = 0` in every state, then
`U′[c(s)] q(s) = β ∫ U′(c[nxt(s, z′)]) R(s, z′) Q(s, dz′)`. With `R(s, z′) = f(z′)` and
`nxt(s, z′) = (g(x, z), z′)` this is (2). -/
theorem ex_16_2_eq2_general (D : MsGenData U c q R nxt B β) {dU : ℝ → ℝ}
    (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) {w : ℝ × Sx → ℝ} (hwm : Measurable w) {C : ℝ}
    (hC : ∀ p ∈ msSecDom c q B, |w p| ≤ C) (hw : MsGBellman U c q R Q nxt B β w)
    (hcv : MsSecConcave c q B w) (hc : ∀ s, 0 < c s)
    (hopt : ∀ s, w (0, s) = msGObj U c q R Q nxt β w 0 s 0) (s : Sx) :
    q s * dU (c s) = β * ∫ z', dU (c (nxt s z')) * R s z' ∂(Q s) := by
  refine msG_foc D hdU hwm hC hw hcv (hc s) (hopt s) fun z' => ?_
  have hpos : 0 < c (nxt s z') - q (nxt s z') * 0 := by
    rw [mul_zero, sub_zero]; exact hc _
  have := ex_16_2d_general D hdU hw hcv D.B_neg.le (hopt _) hpos
  rwa [mul_zero, sub_zero] at this

/-- **Exercise 16.2(g)**, general shock space: for an asset paying the dividend `f(s′)` with
ex-dividend price `q`, the return is `R(s, z′) = f(s′) + q(s′)`, and no trade in every state gives
(3): `U′[c(s)] q(s) = β ∫ U′(c[s′]) {f[s′] + q[s′]} Q(s, dz′)`, `s′ = nxt(s, z′)`. -/
theorem ex_16_2g_general {f : Sx → ℝ}
    (D : MsGenData U c q (fun s z' => f (nxt s z') + q (nxt s z')) nxt B β) {dU : ℝ → ℝ}
    (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) {w : ℝ × Sx → ℝ} (hwm : Measurable w) {C : ℝ}
    (hC : ∀ p ∈ msSecDom c q B, |w p| ≤ C)
    (hw : MsGBellman U c q (fun s z' => f (nxt s z') + q (nxt s z')) Q nxt B β w)
    (hcv : MsSecConcave c q B w) (hc : ∀ s, 0 < c s)
    (hopt : ∀ s, w (0, s) =
      msGObj U c q (fun s z' => f (nxt s z') + q (nxt s z')) Q nxt β w 0 s 0) (s : Sx) :
    dU (c s) * q s =
      β * ∫ z', dU (c (nxt s z')) * (f (nxt s z') + q (nxt s z')) ∂(Q s) := by
  rw [mul_comm]
  exact ex_16_2_eq2_general D hdU hwm hC hw hcv hc hopt s

/-! ### The converse of Exercise 16.2(d): the equilibrium price makes no trade optimal -/

/-- The key step of the verification argument: if `w(A′, s′) ≤ w(0, s′) + U′(c(s′))A′ + E` on `D`,
then the objective of (1) at `(A, s)` is at most `w(0, s) + U′(c(s))A + βE` (tangent inequality,
Bellman equation and (2)). -/
theorem msG_super_step (D : MsGenData U c q R nxt B β) (hU : ConcaveOn ℝ (Ici 0) U)
    {dU : ℝ → ℝ} (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) (hc : ∀ s, 0 < c s)
    (h2 : ∀ s, q s * dU (c s) = β * ∫ z', dU (c (nxt s z')) * R s z' ∂(Q s))
    (hint : ∀ s, Integrable (fun z' => dU (c (nxt s z')) * R s z') (Q s))
    {w : ℝ × Sx → ℝ} (hwm : Measurable w) {C : ℝ} (hC : ∀ p ∈ msSecDom c q B, |w p| ≤ C)
    (hw : MsGBellman U c q R Q nxt B β w) {E : ℝ}
    (hE : ∀ A s, q s * B - c s ≤ A → w (A, s) ≤ w (0, s) + dU (c s) * A + E)
    {A : ℝ} {s : Sx} {b : ℝ} (hb : B ≤ b) (hbf : q s * b ≤ c s + A) :
    msGObj U c q R Q nxt β w A s b ≤ w (0, s) + dU (c s) * A + β * E := by
  have hq := D.q_pos s
  have h0dom : q s * B - c s ≤ 0 := by nlinarith [D.B_neg, hc s]
  have hge0 := (hw 0 s h0dom).1 0 D.B_neg.le (by rw [mul_zero, add_zero]; exact (hc s).le)
  have hE0 : msGE R Q nxt w s 0 = ∫ z', w (0, nxt s z') ∂(Q s) := by
    simp only [msGE, zero_mul]
  simp only [msGObj, add_zero, mul_zero, sub_zero, hE0] at hge0
  have ht := gc_concave_le_tangent hU (hc s) (by linarith : (0 : ℝ) ≤ c s + A - q s * b)
    (hdU _ (hc s))
  have i0 := msG_integrable_zero (Q := Q) D hwm hC s
  have ib := msG_integrable (Q := Q) D hwm hC s hb
  have hsum : msGE R Q nxt w s b ≤ ∫ z', w (0, nxt s z') ∂(Q s) +
      b * ∫ z', dU (c (nxt s z')) * R s z' ∂(Q s) + E := by
    have hle : msGE R Q nxt w s b ≤ ∫ z', (w (0, nxt s z') +
        b * (dU (c (nxt s z')) * R s z') + E) ∂(Q s) := by
      unfold msGE
      refine integral_mono ib ((i0.add ((hint s).const_mul b)).add (integrable_const E))
        fun z' => ?_
      have h := hE _ _ (msG_next_mem D s hb z')
      have e : dU (c (nxt s z')) * (b * R s z') = b * (dU (c (nxt s z')) * R s z') := by ring
      change w (b * R s z', nxt s z') ≤ w (0, nxt s z') + b * (dU (c (nxt s z')) * R s z') + E
      linarith
    have i1 : Integrable (fun z' => w (0, nxt s z') + b * (dU (c (nxt s z')) * R s z')) (Q s) :=
      i0.add ((hint s).const_mul b)
    have i2 : Integrable (fun z' => b * (dU (c (nxt s z')) * R s z')) (Q s) :=
      (hint s).const_mul b
    rwa [integral_add i1 (integrable_const E), integral_add i0 i2, integral_const_mul,
      integral_const, probReal_univ, one_smul] at hle
  have e2 := h2 s
  have hβ := D.beta_pos
  simp only [msGObj]
  have key : β * (b * ∫ z', dU (c (nxt s z')) * R s z' ∂(Q s)) = b * (q s * dU (c s)) := by
    rw [e2]; ring
  nlinarith [mul_le_mul_of_nonneg_left hsum hβ.le]

/-- **The supergradient inequality**, general shock space: if `q` satisfies (2) in every state
(with `U′(c(s′)) R(s, ·)` integrable), every measurable solution `w` of (1) bounded on `D`
satisfies `w(A, s) ≤ w(0, s) + U′(c(s))A` on `D`. -/
theorem msG_supergradient (D : MsGenData U c q R nxt B β) (hU : ConcaveOn ℝ (Ici 0) U)
    {dU : ℝ → ℝ} (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) (hdUpos : ∀ x, 0 < x → 0 < dU x)
    (hc : ∀ s, 0 < c s)
    (h2 : ∀ s, q s * dU (c s) = β * ∫ z', dU (c (nxt s z')) * R s z' ∂(Q s))
    (hint : ∀ s, Integrable (fun z' => dU (c (nxt s z')) * R s z') (Q s))
    (hK : ∃ K, ∀ s, dU (c s) * (c s - q s * B) ≤ K) {w : ℝ × Sx → ℝ} (hwm : Measurable w)
    {C : ℝ} (hC : ∀ p ∈ msSecDom c q B, |w p| ≤ C) (hw : MsGBellman U c q R Q nxt B β w) :
    ∀ A s, q s * B - c s ≤ A → w (A, s) ≤ w (0, s) + dU (c s) * A := by
  obtain ⟨K, hK⟩ := hK
  set M := 2 * C + max K 0 with hM
  have key : ∀ n : ℕ, ∀ A s, q s * B - c s ≤ A →
      w (A, s) ≤ w (0, s) + dU (c s) * A + β ^ n * M := by
    intro n
    induction n with
    | zero =>
      intro A s hA
      have hq := D.q_pos s
      have h0dom : q s * B - c s ≤ 0 := by nlinarith [D.B_neg, hc s]
      have h1 := (abs_le.1 (hC (A, s) hA)).2
      have h2' := (abs_le.1 (hC (0, s) h0dom)).1
      have hd := hdUpos _ (hc s)
      have hKs := hK s
      have : -(dU (c s) * A) ≤ max K 0 := by
        rcases le_total A 0 with hneg | hpos
        · have : -(dU (c s) * A) ≤ dU (c s) * (c s - q s * B) := by nlinarith
          exact this.trans (hKs.trans (le_max_left _ _))
        · have : -(dU (c s) * A) ≤ 0 := by nlinarith
          exact this.trans (le_max_right _ _)
      rw [pow_zero, one_mul, hM]
      linarith
    | succ n ih =>
      intro A s hA
      obtain ⟨b, hb, hbf, e⟩ := (hw A s hA).2
      have := msG_super_step D hU hdU hc h2 hint hwm hC hw ih hb hbf
      rw [e, pow_succ, mul_comm (β ^ n) β, mul_assoc]
      exact this
  intro A s hA
  have hlim : Tendsto (fun n : ℕ => w (0, s) + dU (c s) * A + β ^ n * M) atTop
      (𝓝 (w (0, s) + dU (c s) * A)) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one D.beta_pos.le D.beta_lt_one).mul_const M)
  exact ge_of_tendsto' hlim fun n => key n A s hA

/-- **Exercise 16.2(d), converse, general shock space**: if the price `q` satisfies the pricing
equation (2) in every state (with `U′(c(s′)) R(s, ·)` integrable), then for every measurable
solution `w` of (1) bounded on `D`, `b = 0` (no trade) is optimal at `A = 0` in every state. -/
theorem ex_16_2d_converse_general (D : MsGenData U c q R nxt B β) (hU : ConcaveOn ℝ (Ici 0) U)
    {dU : ℝ → ℝ} (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x) (hdUpos : ∀ x, 0 < x → 0 < dU x)
    (hc : ∀ s, 0 < c s)
    (h2 : ∀ s, q s * dU (c s) = β * ∫ z', dU (c (nxt s z')) * R s z' ∂(Q s))
    (hint : ∀ s, Integrable (fun z' => dU (c (nxt s z')) * R s z') (Q s))
    (hK : ∃ K, ∀ s, dU (c s) * (c s - q s * B) ≤ K) {w : ℝ × Sx → ℝ} (hwm : Measurable w)
    {C : ℝ} (hC : ∀ p ∈ msSecDom c q B, |w p| ≤ C) (hw : MsGBellman U c q R Q nxt B β w)
    (s : Sx) : w (0, s) = msGObj U c q R Q nxt β w 0 s 0 := by
  have hsup := msG_supergradient D hU hdU hdUpos hc h2 hint hK hwm hC hw
  have hq := D.q_pos s
  have h0dom : q s * B - c s ≤ 0 := by nlinarith [D.B_neg, hc s]
  obtain ⟨b, hb, hbf, e⟩ := (hw 0 s h0dom).2
  have hge := (hw 0 s h0dom).1 0 D.B_neg.le (by rw [mul_zero, add_zero]; exact (hc s).le)
  have hE0 : msGE R Q nxt w s 0 = ∫ z', w (0, nxt s z') ∂(Q s) := by
    simp only [msGE, zero_mul]
  have hge0 : msGObj U c q R Q nxt β w 0 s 0 = U (c s) + β * ∫ z', w (0, nxt s z') ∂(Q s) := by
    simp only [msGObj, add_zero, mul_zero, sub_zero, hE0]
  apply le_antisymm _ hge
  rw [e]
  have ht := gc_concave_le_tangent hU (hc s) (by linarith : (0 : ℝ) ≤ c s + 0 - q s * b)
    (hdU _ (hc s))
  have i0 := msG_integrable_zero (Q := Q) D hwm hC s
  have ib := msG_integrable (Q := Q) D hwm hC s hb
  have hsum : msGE R Q nxt w s b ≤ ∫ z', w (0, nxt s z') ∂(Q s) +
      b * ∫ z', dU (c (nxt s z')) * R s z' ∂(Q s) := by
    have hle : msGE R Q nxt w s b ≤
        ∫ z', (w (0, nxt s z') + b * (dU (c (nxt s z')) * R s z')) ∂(Q s) := by
      unfold msGE
      refine integral_mono ib (i0.add ((hint s).const_mul b)) fun z' => ?_
      have h := hsup _ _ (msG_next_mem D s hb z')
      have e : dU (c (nxt s z')) * (b * R s z') = b * (dU (c (nxt s z')) * R s z') := by ring
      change w (b * R s z', nxt s z') ≤ w (0, nxt s z') + b * (dU (c (nxt s z')) * R s z')
      linarith
    have i2 : Integrable (fun z' => b * (dU (c (nxt s z')) * R s z')) (Q s) :=
      (hint s).const_mul b
    rwa [integral_add i0 i2, integral_const_mul] at hle
  have key : β * (b * ∫ z', dU (c (nxt s z')) * R s z' ∂(Q s)) = b * (q s * dU (c s)) := by
    rw [h2 s]; ring
  rw [hge0]
  simp only [msGObj]
  nlinarith [mul_le_mul_of_nonneg_left hsum D.beta_pos.le]

/-- **In equilibrium the book's (d) holds**, general shock space: if `q` satisfies (2) in every
state and `w` (measurable, bounded on `D`, concave in `A`) solves (1), then `w(·, s)` is
differentiable at `0` with `w₁(0, s) = U′(c(s))`. -/
theorem ex_16_2d_equilibrium_general (D : MsGenData U c q R nxt B β)
    (hUs : StrictConcaveOn ℝ (Ici 0) U) {dU : ℝ → ℝ} (hdU : ∀ x, 0 < x → HasDerivAt U (dU x) x)
    (hdUpos : ∀ x, 0 < x → 0 < dU x) (hc : ∀ s, 0 < c s)
    (h2 : ∀ s, q s * dU (c s) = β * ∫ z', dU (c (nxt s z')) * R s z' ∂(Q s))
    (hint : ∀ s, Integrable (fun z' => dU (c (nxt s z')) * R s z') (Q s))
    (hK : ∃ K, ∀ s, dU (c s) * (c s - q s * B) ≤ K) {w : ℝ × Sx → ℝ} (hwm : Measurable w)
    {C : ℝ} (hC : ∀ p ∈ msSecDom c q B, |w p| ≤ C) (hw : MsGBellman U c q R Q nxt B β w)
    (hcv : MsSecConcave c q B w) (s : Sx) :
    HasDerivAt (fun A => w (A, s)) (dU (c s)) 0 := by
  have hopt := ex_16_2d_converse_general D hUs.concaveOn hdU hdUpos hc h2 hint hK hwm hC hw s
  have := ex_16_2d_general D hdU hw hcv (s := s) D.B_neg.le hopt
    (by rw [mul_zero, sub_zero]; exact hc s)
  rwa [mul_zero, sub_zero] at this

end StokeyLucasPrescott.EquilibriumApplications
