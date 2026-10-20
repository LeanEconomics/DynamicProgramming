/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriumApplications.ManySectorPrices
import EquilibriumApplications.GrowthCertaintyRecursive

/-!
# Pricing securities: the consumer's functional equation (1) of §16.2 (Exercise 16.2(c))

SLP §16.2, pp. 482–483. The state is `s = (x, z)`; next period's state is `nxt s z′ = (g(x, z), z′)`
with probability `π s z′ = Q(z, z′)`. Here the shock space is **finite** (see the Correction). A
consumer with a claim to `A` units of current consumption (on top of the endowment `c(s)`) buys `b`
units of a security at price `q(s)`, paying `R s z′ ≥ 0` next period (`R = f(z′)` for a one-period
security; `R = f(s′) + q(s′)` for the multi-period asset of Ex 16.2g), with credit limit `B < 0`:

  (1) `w(A, s) = max {U(c(s) + A − q(s) b) + β Σ_{z′} π(s, z′) w(b R(s, z′), nxt s z′) :
        b ≥ B, q(s) b ≤ c(s) + A}`.

* `MsSecData`: the data (`U` bounded continuous, `c`, `q > 0`, `R ≥ 0`, `π`, `nxt` continuous in
  `s`), with the **domain condition** `q(s′)B − c(s′) ≤ B R(s, z′)`.
* `msSecDom`: the domain `D = {(A, s) : A ≥ q(s)B − c(s)}` where the constraint set is nonempty;
  `msSecObj`, `MsSecBellman` (equation (1) on `D`, with "max").
* `ms_secBellman_unique`: at most one solution of (1) bounded on `D` (`|w − w′| ≤ βⁿ C`).
* `msSecT`, `msSecTB`, `ms_secTB_contracting`: the operator of (1) on bounded continuous functions
  (choices `b = B + r · gap`, `r ∈ [0, 1]`), a contraction of modulus `β`.
* **Exercise 16.2(c)** (`ex_16_2c`): there is a bounded continuous `w` satisfying (1) on `D`, and
  every solution of (1) bounded on `D` agrees with it on `D`.
* `ex_16_2c_domain_counterexample`: without the domain condition a feasible choice can lead out of
  `D` (`c = 1/10`, `q = 1/2`, `R = 1`, `B = −1`): (1) is then not a functional equation on `D`.

**Corrections (NOTE to Ex 16.2c).**
* The price function `q` must be given (any continuous `q > 0`); in equilibrium it is (2).
* `w` is defined only on `D`, and transitions can leave `D` unless `B` is restricted: the domain
  condition above is added (`ex_16_2c_domain_counterexample` shows it is needed).
* Continuity of `z ↦ ∫ w[b f(z′), g(x, z), z′] Q(z, dz′)` fails for a merely Feller `Q` and
  measurable `f`; here the shock space is finite (or, equivalently, `Q` has finite support), which
  removes the issue. The general measurable case is not formalised.
-/

namespace StokeyLucasPrescott.EquilibriumApplications

open Filter Topology Set
open scoped BoundedContinuousFunction

variable {Sx : Type*} [TopologicalSpace Sx] {Zf : Type*} [Fintype Zf]

variable (U : ℝ → ℝ) (c q : Sx → ℝ) (R π : Sx → Zf → ℝ) (nxt : Sx → Zf → Sx) in
/-- The data of (1) (p. 483), with the domain condition `q(s′)B − c(s′) ≤ B R(s, z′)`. -/
structure MsSecData (B β : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  B_neg : B < 0
  U_cont : Continuous U
  U_bdd : ∃ M, ∀ x, |U x| ≤ M
  c_cont : Continuous c
  q_cont : Continuous q
  q_pos : ∀ s, 0 < q s
  R_cont : ∀ z', Continuous fun s => R s z'
  R_nonneg : ∀ s z', 0 ≤ R s z'
  π_cont : ∀ z', Continuous fun s => π s z'
  π_nonneg : ∀ s z', 0 ≤ π s z'
  π_sum : ∀ s, ∑ z', π s z' = 1
  nxt_cont : ∀ z', Continuous fun s => nxt s z'
  dom : ∀ s z', q (nxt s z') * B - c (nxt s z') ≤ B * R s z'

/-- The domain `D = {(A, s) : A ≥ q(s)B − c(s)}` of (1). -/
def msSecDom (c q : Sx → ℝ) (B : ℝ) : Set (ℝ × Sx) := {p | q p.2 * B - c p.2 ≤ p.1}

/-- The objective of (1) at `(A, s)` for the purchase `b`. -/
noncomputable def msSecObj (U : ℝ → ℝ) (c q : Sx → ℝ) (R π : Sx → Zf → ℝ) (nxt : Sx → Zf → Sx)
    (β : ℝ) (w : ℝ × Sx → ℝ) (A : ℝ) (s : Sx) (b : ℝ) : ℝ :=
  U (c s + A - q s * b) + β * ∑ z', π s z' * w (b * R s z', nxt s z')

/-- `w` **satisfies (1) on `D`** (with "max"). -/
def MsSecBellman (U : ℝ → ℝ) (c q : Sx → ℝ) (R π : Sx → Zf → ℝ) (nxt : Sx → Zf → Sx) (B β : ℝ)
    (w : ℝ × Sx → ℝ) : Prop :=
  ∀ A s, q s * B - c s ≤ A →
    (∀ b, B ≤ b → q s * b ≤ c s + A → msSecObj U c q R π nxt β w A s b ≤ w (A, s)) ∧
    ∃ b, B ≤ b ∧ q s * b ≤ c s + A ∧ w (A, s) = msSecObj U c q R π nxt β w A s b

variable {U : ℝ → ℝ} {c q : Sx → ℝ} {R π : Sx → Zf → ℝ} {nxt : Sx → Zf → Sx} {B β : ℝ}

/-- Feasible purchases lead to states in `D` (the domain condition). -/
theorem ms_sec_next_mem (D : MsSecData U c q R π nxt B β) (s : Sx) {b : ℝ} (hb : B ≤ b)
    (z' : Zf) : (b * R s z', nxt s z') ∈ msSecDom c q B := by
  have h1 := D.dom s z'
  have h2 := D.R_nonneg s z'
  change q (nxt s z') * B - c (nxt s z') ≤ b * R s z'
  nlinarith

/-- `|Σ π (u − v)| ≤ C` when `|u − v| ≤ C` termwise. -/
theorem ms_sec_sum_sub_le (D : MsSecData U c q R π nxt B β) (s : Sx) {u v : Zf → ℝ} {C : ℝ}
    (h : ∀ z', |u z' - v z'| ≤ C) :
    |∑ z', π s z' * u z' - ∑ z', π s z' * v z'| ≤ C := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ z', (π s z' * u z' - π s z' * v z')| ≤ ∑ z', |π s z' * u z' - π s z' * v z'| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z', π s z' * |u z' - v z'| := by
        congr 1; ext z'
        rw [← mul_sub, abs_mul, abs_of_nonneg (D.π_nonneg s z')]
    _ ≤ ∑ z', π s z' * C := Finset.sum_le_sum fun z' _ =>
        mul_le_mul_of_nonneg_left (h z') (D.π_nonneg s z')
    _ = C := by rw [← Finset.sum_mul, D.π_sum, one_mul]

/-- **At most one solution of (1) bounded on `D`**: `|w − w′| ≤ βⁿ C` on `D` for every `n`. -/
theorem ms_secBellman_unique (D : MsSecData U c q R π nxt B β) {w w' : ℝ × Sx → ℝ}
    (hw : MsSecBellman U c q R π nxt B β w) (hw' : MsSecBellman U c q R π nxt B β w') {C : ℝ}
    (hC : ∀ p ∈ msSecDom c q B, |w p - w' p| ≤ C) : ∀ p ∈ msSecDom c q B, w p = w' p := by
  have key : ∀ n, ∀ p ∈ msSecDom c q B, |w p - w' p| ≤ β ^ n * C := by
    intro n
    induction n with
    | zero => intro p hp; rw [pow_zero, one_mul]; exact hC p hp
    | succ n ih =>
      rintro ⟨A, s⟩ hp
      obtain ⟨b₁, hb₁, hf₁, e₁⟩ := (hw A s hp).2
      obtain ⟨b₂, hb₂, hf₂, e₂⟩ := (hw' A s hp).2
      have a1 := (hw' A s hp).1 b₁ hb₁ hf₁
      have a2 := (hw A s hp).1 b₂ hb₂ hf₂
      have d1 := ms_sec_sum_sub_le D s (u := fun z' => w (b₁ * R s z', nxt s z'))
        (v := fun z' => w' (b₁ * R s z', nxt s z')) fun z' => ih _ (ms_sec_next_mem D s hb₁ z')
      have d2 := ms_sec_sum_sub_le D s (u := fun z' => w (b₂ * R s z', nxt s z'))
        (v := fun z' => w' (b₂ * R s z', nxt s z')) fun z' => ih _ (ms_sec_next_mem D s hb₂ z')
      simp only [msSecObj] at e₁ e₂ a1 a2
      have hβ := D.beta_pos
      rw [pow_succ, mul_comm (β ^ n) β, mul_assoc]
      refine abs_le.2 ⟨?_, ?_⟩
      · nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 d2).1 hβ.le]
      · nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 d1).2 hβ.le]
  intro p hp
  have hlim : Tendsto (fun n : ℕ => β ^ n * C) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one D.beta_pos.le D.beta_lt_one).mul_const C
  have : |w p - w' p| ≤ 0 := ge_of_tendsto' hlim fun n => key n p hp
  exact sub_eq_zero.1 (abs_nonpos_iff.1 this)

/-! ### Existence: the operator of (1) -/

/-- The purchase `b = B + r · max {0, (c(s) + A)/q(s) − B}`, `r ∈ [0, 1]`: all of `[B, (c + A)/q]`
on `D`, and the constant `B` off `D`. -/
noncomputable def msSecB (c q : Sx → ℝ) (B : ℝ) (A : ℝ) (s : Sx) (r : ℝ) : ℝ :=
  B + r * max 0 ((c s + A) / q s - B)

/-- **The operator of (1)**: `(Tw)(A, s) = max_{r ∈ [0,1]} {objective at b = msSecB A s r}`. -/
noncomputable def msSecT (U : ℝ → ℝ) (c q : Sx → ℝ) (R π : Sx → Zf → ℝ) (nxt : Sx → Zf → Sx)
    (B β : ℝ) (w : ℝ × Sx → ℝ) (p : ℝ × Sx) : ℝ :=
  sSup ((fun r => msSecObj U c q R π nxt β w p.1 p.2 (msSecB c q B p.1 p.2 r)) '' Icc 0 1)

/-- The objective of (1) along `b = msSecB A s r` is jointly continuous. -/
theorem msSecObj_continuous (D : MsSecData U c q R π nxt B β) {w : ℝ × Sx → ℝ}
    (hw : Continuous w) : Continuous fun r : (ℝ × Sx) × ℝ =>
      msSecObj U c q R π nxt β w r.1.1 r.1.2 (msSecB c q B r.1.1 r.1.2 r.2) := by
  have hc : Continuous fun r : (ℝ × Sx) × ℝ => c r.1.2 :=
    D.c_cont.comp (continuous_snd.comp continuous_fst)
  have hq : Continuous fun r : (ℝ × Sx) × ℝ => q r.1.2 :=
    D.q_cont.comp (continuous_snd.comp continuous_fst)
  have hA : Continuous fun r : (ℝ × Sx) × ℝ => r.1.1 := continuous_fst.comp continuous_fst
  have hb : Continuous fun r : (ℝ × Sx) × ℝ => msSecB c q B r.1.1 r.1.2 r.2 :=
    continuous_const.add (continuous_snd.mul (continuous_const.max
      (((hc.add hA).div hq fun r => (D.q_pos _).ne').sub continuous_const)))
  unfold msSecObj
  refine (D.U_cont.comp ((hc.add hA).sub (hq.mul hb))).add (continuous_const.mul
    (continuous_finsetSum _ fun z' _ => ?_))
  exact ((D.π_cont z').comp (continuous_snd.comp continuous_fst)).mul
    (hw.comp ((hb.mul ((D.R_cont z').comp (continuous_snd.comp continuous_fst))).prodMk
      ((D.nxt_cont z').comp (continuous_snd.comp continuous_fst))))

/-- The objective of (1) is bounded by `M + β C` when `|U| ≤ M`, `|w| ≤ C`. -/
theorem msSecObj_abs_le (D : MsSecData U c q R π nxt B β) {M : ℝ} (hM : ∀ x, |U x| ≤ M)
    {w : ℝ × Sx → ℝ} {C : ℝ} (hC : ∀ p, |w p| ≤ C) (A : ℝ) (s : Sx) (b : ℝ) :
    |msSecObj U c q R π nxt β w A s b| ≤ M + β * C := by
  have h0 := ms_sec_sum_sub_le D s (u := fun z' => w (b * R s z', nxt s z')) (v := fun _ => 0)
    fun z' => by simpa using hC (b * R s z', nxt s z')
  simp only [mul_zero, Finset.sum_const_zero, sub_zero] at h0
  unfold msSecObj
  calc |U (c s + A - q s * b) + β * ∑ z', π s z' * w (b * R s z', nxt s z')|
      ≤ |U (c s + A - q s * b)| + |β * ∑ z', π s z' * w (b * R s z', nxt s z')| :=
        abs_add_le _ _
    _ ≤ M + β * C := by
        rw [abs_mul, abs_of_pos D.beta_pos]
        exact add_le_add (hM _) (mul_le_mul_of_nonneg_left h0 D.beta_pos.le)

/-- The maximum defining `Tw` is attained. -/
theorem msSecT_attained (D : MsSecData U c q R π nxt B β) {w : ℝ × Sx → ℝ} (hw : Continuous w)
    (p : ℝ × Sx) : ∃ r ∈ Icc (0 : ℝ) 1,
      msSecT U c q R π nxt B β w p = msSecObj U c q R π nxt β w p.1 p.2 (msSecB c q B p.1 p.2 r) :=
  isCompact_Icc.exists_sSup_image_eq (nonempty_Icc.2 zero_le_one)
    ((msSecObj_continuous D hw).comp (continuous_const.prodMk continuous_id)).continuousOn

/-- `Tw` dominates the objective at every `r ∈ [0, 1]`. -/
theorem msSecT_ge (D : MsSecData U c q R π nxt B β) {w : ℝ × Sx → ℝ} (hw : Continuous w)
    (p : ℝ × Sx) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    msSecObj U c q R π nxt β w p.1 p.2 (msSecB c q B p.1 p.2 r) ≤ msSecT U c q R π nxt B β w p :=
  le_csSup (isCompact_Icc.image ((msSecObj_continuous D hw).comp
    (continuous_const.prodMk continuous_id))).bddAbove (mem_image_of_mem _ hr)

/-- On `D` every feasible purchase is `msSecB A s r` for some `r ∈ [0, 1]`. -/
theorem msSecB_surj (D : MsSecData U c q R π nxt B β) {A : ℝ} {s : Sx}
    (hp : q s * B - c s ≤ A) {b : ℝ} (hb : B ≤ b) (hf : q s * b ≤ c s + A) :
    ∃ r ∈ Icc (0 : ℝ) 1, msSecB c q B A s r = b := by
  have hq := D.q_pos s
  have hgap : 0 ≤ (c s + A) / q s - B := by
    rw [sub_nonneg, le_div_iff₀ hq]; linarith
  have hbB : b ≤ (c s + A) / q s := by rw [le_div_iff₀ hq]; linarith
  rcases hgap.lt_or_eq with hlt | heq
  · refine ⟨(b - B) / ((c s + A) / q s - B), ⟨div_nonneg (by linarith) hlt.le,
      (div_le_one hlt).2 (by linarith)⟩, ?_⟩
    rw [msSecB, max_eq_right hlt.le, div_mul_cancel₀ _ hlt.ne']
    ring
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [msSecB, zero_mul, add_zero]
    linarith

/-- On `D`, `msSecB A s r` is feasible for `r ∈ [0, 1]`. -/
theorem msSecB_feasible (D : MsSecData U c q R π nxt B β) {A : ℝ} {s : Sx}
    (hp : q s * B - c s ≤ A) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    B ≤ msSecB c q B A s r ∧ q s * msSecB c q B A s r ≤ c s + A := by
  have hq := D.q_pos s
  have hgap : 0 ≤ (c s + A) / q s - B := by
    rw [sub_nonneg, le_div_iff₀ hq]; linarith
  simp only [msSecB, max_eq_right hgap]
  refine ⟨by nlinarith [hr.1], ?_⟩
  have h1 : B + r * ((c s + A) / q s - B) ≤ (c s + A) / q s := by nlinarith [hr.2]
  rw [le_div_iff₀ hq] at h1
  linarith

/-- `Tw` is continuous. -/
theorem msSecT_continuous (D : MsSecData U c q R π nxt B β) {w : ℝ × Sx → ℝ}
    (hw : Continuous w) : Continuous (msSecT U c q R π nxt B β w) :=
  isCompact_Icc.continuous_sSup (msSecObj_continuous D hw)

/-- The operator of (1) on bounded continuous functions on `ℝ × S`. -/
noncomputable def msSecTB (D : MsSecData U c q R π nxt B β) (w : ℝ × Sx →ᵇ ℝ) : ℝ × Sx →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (msSecT U c q R π nxt B β w)
    (msSecT_continuous D w.continuous) (Classical.choose D.U_bdd + β * ‖w‖) fun p => by
      rw [Real.norm_eq_abs]
      obtain ⟨r, -, e⟩ := msSecT_attained D w.continuous p
      rw [e]
      exact msSecObj_abs_le D (Classical.choose_spec D.U_bdd)
        (fun p => by rw [← Real.norm_eq_abs]; exact w.norm_coe_le_norm p) _ _ _

/-- Values of `msSecTB`. -/
theorem msSecTB_apply (D : MsSecData U c q R π nxt B β) (w : ℝ × Sx →ᵇ ℝ) (p : ℝ × Sx) :
    msSecTB D w p = msSecT U c q R π nxt B β w p := rfl

/-- **Blackwell**: the operator of (1) is a contraction of modulus `β`. -/
theorem ms_secTB_contracting (D : MsSecData U c q R π nxt B β) :
    ContractingWith ⟨β, D.beta_pos.le⟩ (msSecTB D) := by
  refine ⟨D.beta_lt_one, LipschitzWith.of_dist_le_mul fun w w' => ?_⟩
  refine (BoundedContinuousFunction.dist_le (mul_nonneg D.beta_pos.le dist_nonneg)).2 fun p => ?_
  rw [Real.dist_eq, msSecTB_apply, msSecTB_apply]
  obtain ⟨r₁, hr₁, e₁⟩ := msSecT_attained D w.continuous p
  obtain ⟨r₂, hr₂, e₂⟩ := msSecT_attained D w'.continuous p
  have a1 := msSecT_ge D w'.continuous p hr₁
  have a2 := msSecT_ge D w.continuous p hr₂
  have hd : ∀ (b : ℝ), |∑ z', π p.2 z' * w (b * R p.2 z', nxt p.2 z') -
      ∑ z', π p.2 z' * w' (b * R p.2 z', nxt p.2 z')| ≤ dist w w' := fun b =>
    ms_sec_sum_sub_le D p.2 fun z' => by
      rw [← Real.dist_eq]; exact BoundedContinuousFunction.dist_coe_le_dist _
  have d1 := hd (msSecB c q B p.1 p.2 r₁)
  have d2 := hd (msSecB c q B p.1 p.2 r₂)
  simp only [msSecObj] at e₁ e₂ a1 a2
  have hβ := D.beta_pos
  refine abs_le.2 ⟨?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 d2).1 hβ.le]
  · nlinarith [mul_le_mul_of_nonneg_left (abs_le.1 d1).2 hβ.le]

/-- A fixed point of the operator satisfies (1) on `D`. -/
theorem ms_secBellman_of_fixed (D : MsSecData U c q R π nxt B β) {w : ℝ × Sx →ᵇ ℝ}
    (hfix : msSecTB D w = w) : MsSecBellman U c q R π nxt B β w := by
  intro A s hp
  have hwp : w (A, s) = msSecT U c q R π nxt B β w (A, s) := by
    rw [← msSecTB_apply D w (A, s), hfix]
  refine ⟨fun b hb hf => ?_, ?_⟩
  · obtain ⟨r, hr, hrb⟩ := msSecB_surj D hp hb hf
    have := msSecT_ge D w.continuous (A, s) hr
    rw [hrb] at this
    rw [hwp]
    exact this
  · obtain ⟨r, hr, e⟩ := msSecT_attained D w.continuous (A, s)
    obtain ⟨h1, h2⟩ := msSecB_feasible D hp hr
    exact ⟨_, h1, h2, hwp.trans e⟩

/-- **Exercise 16.2(c)** (finite shocks, given `q`, with the domain condition): there is a bounded
continuous `w` satisfying (1) on `D`, and every solution of (1) that is bounded on `D` agrees with
it on `D`. -/
theorem ex_16_2c (D : MsSecData U c q R π nxt B β) :
    ∃ w : ℝ × Sx →ᵇ ℝ, MsSecBellman U c q R π nxt B β w ∧
      ∀ w' : ℝ × Sx → ℝ, (∃ C, ∀ p ∈ msSecDom c q B, |w' p| ≤ C) →
        MsSecBellman U c q R π nxt B β w' → ∀ p ∈ msSecDom c q B, w' p = w p := by
  set w := ContractingWith.fixedPoint (α := ℝ × Sx →ᵇ ℝ) (msSecTB D) (ms_secTB_contracting D)
  have hfix : msSecTB D w = w := (ms_secTB_contracting D).fixedPoint_isFixedPt
  refine ⟨w, ms_secBellman_of_fixed D hfix, fun w' ⟨C, hC⟩ hw' => ?_⟩
  refine ms_secBellman_unique D hw' (ms_secBellman_of_fixed D hfix) (C := C + ‖w‖) fun p hp => ?_
  have h2 : |w p| ≤ ‖w‖ := by
    rw [← Real.norm_eq_abs]
    exact w.norm_coe_le_norm p
  calc |w' p - w p| ≤ |w' p| + |w p| := abs_sub _ _
    _ ≤ C + ‖w‖ := add_le_add (hC p hp) h2

/-- **Counterexample** (NOTE (ii) to Ex 16.2c): with a constant state, `c = 1/10`, `q = 1/2`,
`R = 1`, `B = −1`, the domain condition fails, and from `A = qB − c ∈ D` the feasible purchase
`b = B` leads to `A′ = bR = −1 < qB − c`, outside `D`. -/
theorem ex_16_2c_domain_counterexample :
    (¬ ∀ (s z' : Unit), (fun _ : Unit => (1 / 2 : ℝ)) ((fun s _ => s) s z') * (-1) -
      (fun _ : Unit => (1 / 10 : ℝ)) ((fun s _ => s) s z') ≤ (-1) * (1 : ℝ)) ∧
    ∃ A : ℝ, ∃ s : Unit, (A, s) ∈ msSecDom (fun _ : Unit => (1 / 10 : ℝ))
        (fun _ : Unit => (1 / 2 : ℝ)) (-1) ∧
      ∃ b : ℝ, (-1 : ℝ) ≤ b ∧ (1 / 2 : ℝ) * b ≤ 1 / 10 + A ∧
        (b * 1, s) ∉
          msSecDom (fun _ : Unit => (1 / 10 : ℝ)) (fun _ : Unit => (1 / 2 : ℝ)) (-1) := by
  refine ⟨fun h => by have := h () (); norm_num at this, -(6 / 10), (), ?_, -1, le_rfl, ?_, ?_⟩
  · change (1 / 2 : ℝ) * (-1) - 1 / 10 ≤ -(6 / 10)
    norm_num
  · norm_num
  · change ¬ ((1 / 2 : ℝ) * (-1) - 1 / 10 ≤ -1 * 1)
    norm_num

end StokeyLucasPrescott.EquilibriumApplications
