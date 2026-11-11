/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RecursiveContracts.HIBasics
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The principal's Bellman equation and Proposition 22.3.1

Miao, §22.3, pp. 789–793: the dynamic program (22.23)–(22.25) in the promised value `v`, its
bounds (22.26), and the contraction part of Proposition 22.3.1.

* `hi_uinv` inverts `u` on `(−∞, sup u)` (`hi_u_uinv`); `hi_cstar v = u⁻¹((1 − β)v)` is the
  first-best consumption `c*(v)` and `hi_b v` the constant transfer `b(v)` with
  `Σ πᵢ u(θᵢ + b) / (1 − β) = v` (`hi_b_spec`).
* `hi_L v = −b(v)/(1 − β)` and `hi_U v = Σ πᵢ [θᵢ − c*(v)]/(1 − β)` are the bounds of (22.26);
  `hi_InF` is the book's space `F` of functions between them on `(−∞, vmax)`;
  `hi_U_sub_L_le`: the gap is at most `(θ̄ − θ₁)/(1 − β)`.
* `hi_T` is the Bellman operator of (22.23): the supremum of the principal's value over the
  contracts feasible at `v`.
* `hi_const_feasible`: the constant contract `cᵢ = b(v)`, `wᵢ = v` is feasible;
  `hi_principal_le_U`: no feasible contract beats the first-best (Jensen's inequality);
  `eq_22_26`: `T` maps `F` into `F`, i.e. `−b/(1 − β) ≤ T f ≤ Σ πᵢ[θᵢ − c*]/(1 − β)`.
* `hi_T_abs_le`: Blackwell's discounting, `|Tf − Tg| ≤ β ε` when `|f − g| ≤ ε`.
* `proposition_22_3_1`: `T` has a fixed point `P` in `F` (the limit of `Tᵏ L`), it is unique in
  `F`, and it is decreasing; `hi_concaveOn_of_tendsto` is the final limit step of the concavity
  argument.

Departures: the book's space is continuous functions; here `F` is all functions between the
bounds (continuity is not needed for the contraction argument). Concavity of `P` is
`proposition_22_3_1_concave` (module `HIConcavity`); strict concavity, differentiability and
uniqueness of the optimal contract are not proved (see `docs/HI-corrections.md`).
-/

namespace Miao.RecursiveContracts

open Finset Filter Topology

/-- Every utility level lies strictly below `sup u`. -/
theorem hi_u_lt_ubar (M : HIModel) (x : ℝ) : M.u x < hi_ubar M :=
  lt_of_lt_of_le (M.u_strictMono (lt_add_one x)) (le_csSup M.u_bddAbove ⟨x + 1, rfl⟩)

/-- `u` maps onto `(−∞, sup u)`. -/
theorem hi_u_surj (M : HIModel) {y : ℝ} (hy : y < hi_ubar M) : ∃ x, M.u x = y := by
  obtain ⟨_, ⟨x0, rfl⟩, h0⟩ := exists_lt_of_lt_csSup (Set.range_nonempty M.u) hy
  have : ∃ x1, M.u x1 < y := by
    by_contra h
    push Not at h
    exact M.u_not_bddBelow ⟨y, by rintro _ ⟨x, rfl⟩; exact h x⟩
  obtain ⟨x1, h1⟩ := this
  exact intermediate_value_univ x1 x0 M.u_cont ⟨h1.le, h0.le⟩

/-- The inverse of `u` on `(−∞, sup u)` (`0` elsewhere). -/
noncomputable def hi_uinv (M : HIModel) (y : ℝ) : ℝ :=
  if h : y < hi_ubar M then Classical.choose (hi_u_surj M h) else 0

/-- `u(u⁻¹(y)) = y` for `y < sup u`. -/
theorem hi_u_uinv (M : HIModel) {y : ℝ} (hy : y < hi_ubar M) : M.u (hi_uinv M y) = y := by
  simp only [hi_uinv, hy, ↓reduceDIte]
  exact Classical.choose_spec (hi_u_surj M hy)

/-- `v < vmax` iff `(1 − β)v < sup u`. -/
theorem hi_lt_vmax_iff (M : HIModel) (v : ℝ) : v < hi_vmax M ↔ (1 - M.β) * v < hi_ubar M := by
  have h : 0 < 1 - M.β := by linarith [M.β_lt_one]
  unfold hi_vmax
  rw [lt_div_iff₀ h, mul_comm]

/-- `Σ πᵢ a = a`. -/
theorem hi_sum_const (M : HIModel) (a : ℝ) : ∑ i, M.prob i * a = a := by
  rw [← Finset.sum_mul, M.prob_sum, one_mul]

/-- Miao, p. 789: the first-best consumption `c*(v)`, `u(c*(v)) = (1 − β)v`. -/
noncomputable def hi_cstar (M : HIModel) (v : ℝ) : ℝ := hi_uinv M ((1 - M.β) * v)

/-- `Σ πᵢ u(θᵢ + b)`. -/
noncomputable def hi_Bfun (M : HIModel) (b : ℝ) : ℝ := ∑ i, M.prob i * M.u (M.θ i + b)

/-- `b ↦ Σ πᵢ u(θᵢ + b)` is strictly increasing. -/
theorem hi_Bfun_strictMono (M : HIModel) : StrictMono (hi_Bfun M) := by
  intro x y hxy
  unfold hi_Bfun
  refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
  exact mul_lt_mul_of_pos_left (M.u_strictMono (by linarith)) (M.prob_pos i)

/-- `u(θ₁ + b) ≤ Σ πᵢ u(θᵢ + b) ≤ u(θₙ + b)`. -/
theorem hi_Bfun_bounds (M : HIModel) (b : ℝ) :
    M.u (M.θ 0 + b) ≤ hi_Bfun M b ∧ hi_Bfun M b ≤ M.u (M.θ (Fin.last M.N) + b) := by
  unfold hi_Bfun
  constructor
  · calc M.u (M.θ 0 + b) = ∑ i, M.prob i * M.u (M.θ 0 + b) := (hi_sum_const M _).symm
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (M.u_strictMono.monotone (by linarith [M.θ_strictMono.monotone (Fin.zero_le i)]))
          (M.prob_pos i).le
  · calc ∑ i, M.prob i * M.u (M.θ i + b)
        ≤ ∑ i, M.prob i * M.u (M.θ (Fin.last M.N) + b) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (M.u_strictMono.monotone (by linarith [M.θ_strictMono.monotone (Fin.le_last i)]))
            (M.prob_pos i).le
      _ = _ := hi_sum_const M _

/-- `b ↦ Σ πᵢ u(θᵢ + b)` maps onto `(−∞, sup u)`. -/
theorem hi_Bfun_surj (M : HIModel) {y : ℝ} (hy : y < hi_ubar M) : ∃ b, hi_Bfun M b = y := by
  obtain ⟨x0, hx0⟩ := hi_u_surj M (show (y + hi_ubar M) / 2 < hi_ubar M by linarith)
  have : ∃ x1, M.u x1 < y := by
    by_contra h
    push Not at h
    exact M.u_not_bddBelow ⟨y, by rintro _ ⟨x, rfl⟩; exact h x⟩
  obtain ⟨x1, h1⟩ := this
  have hc : Continuous (hi_Bfun M) := by
    unfold hi_Bfun
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul (M.u_cont.comp (continuous_const.add continuous_id))
  have a0 := (hi_Bfun_bounds M (x0 - M.θ 0)).1
  have a1 := (hi_Bfun_bounds M (x1 - M.θ (Fin.last M.N))).2
  rw [add_sub_cancel] at a0 a1
  exact intermediate_value_univ (x1 - M.θ (Fin.last M.N)) (x0 - M.θ 0) hc
    ⟨by linarith, by linarith⟩

/-- Miao, p. 789: the constant transfer `b(v)`, `Σ πᵢ u(θᵢ + b(v)) / (1 − β) = v`. -/
noncomputable def hi_b (M : HIModel) (v : ℝ) : ℝ :=
  if h : (1 - M.β) * v < hi_ubar M then Classical.choose (hi_Bfun_surj M h) else 0

/-- Miao, p. 789: `Σ πᵢ u(θᵢ + b(v)) = (1 − β)v` for `v < vmax`. -/
theorem hi_b_spec (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    hi_Bfun M (hi_b M v) = (1 - M.β) * v := by
  have h := (hi_lt_vmax_iff M v).1 hv
  simp only [hi_b, h, ↓reduceDIte]
  exact Classical.choose_spec (hi_Bfun_surj M h)

/-- `u(c*(v)) = (1 − β)v` for `v < vmax`. -/
theorem hi_cstar_spec (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    M.u (hi_cstar M v) = (1 - M.β) * v :=
  hi_u_uinv M ((hi_lt_vmax_iff M v).1 hv)

/-- `θ̄ = Σ πᵢ θᵢ`. -/
noncomputable def hi_θbar (M : HIModel) : ℝ := ∑ i, M.prob i * M.θ i

/-- Miao, (22.26), p. 789: the lower bound `−b(v)/(1 − β)`. -/
noncomputable def hi_L (M : HIModel) (v : ℝ) : ℝ := -hi_b M v / (1 - M.β)

/-- Miao, (22.26), p. 789: the first-best upper bound `Σ πᵢ [θᵢ − c*(v)]/(1 − β)`. -/
noncomputable def hi_U (M : HIModel) (v : ℝ) : ℝ := (hi_θbar M - hi_cstar M v) / (1 - M.β)

/-- The upper bound written as in (22.26): `Σ πᵢ [θᵢ − c*(v)]/(1 − β)`. -/
theorem hi_U_eq_sum (M : HIModel) (v : ℝ) :
    hi_U M v = ∑ i, M.prob i * (M.θ i - hi_cstar M v) / (1 - M.β) := by
  unfold hi_U hi_θbar
  rw [← Finset.sum_div]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib, hi_sum_const]

/-- Miao, p. 791: the space `F` of functions lying between the bounds (22.26) on
`(−∞, vmax)`. -/
def hi_InF (M : HIModel) (f : ℝ → ℝ) : Prop :=
  ∀ v < hi_vmax M, hi_L M v ≤ f v ∧ f v ≤ hi_U M v

/-- The gap bound of p. 791: `θ₁ + b(v) ≤ c*(v)`. -/
theorem hi_b_le_cstar (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    M.θ 0 + hi_b M v ≤ hi_cstar M v := by
  have h1 := (hi_Bfun_bounds M (hi_b M v)).1
  rw [hi_b_spec M hv, ← hi_cstar_spec M hv] at h1
  exact M.u_strictMono.le_iff_le.1 h1

/-- Miao, p. 791: "the gap between these bounds is bounded": `U(v) − L(v) ≤ (θ̄ − θ₁)/(1 − β)`. -/
theorem hi_U_sub_L_le (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    hi_U M v - hi_L M v ≤ (hi_θbar M - M.θ 0) / (1 - M.β) := by
  have h := hi_b_le_cstar M hv
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  unfold hi_U hi_L
  rw [div_sub_div_same, div_le_div_iff_of_pos_right h1]
  linarith

/-- The agent's value of a contract with `wᵢ < vmax` lies below `vmax`. -/
theorem hi_agentValue_lt_vmax (M : HIModel) {c w : Fin (M.N + 1) → ℝ}
    (hw : ∀ i, w i < hi_vmax M) : hi_agentValue M c w < hi_vmax M := by
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have key : hi_agentValue M c w < ∑ i, M.prob i * (hi_ubar M + M.β * hi_vmax M) := by
    unfold hi_agentValue
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
    have := hi_u_lt_ubar M (M.θ i + c i)
    have := mul_lt_mul_of_pos_left (hw i) M.β_pos
    exact mul_lt_mul_of_pos_left (by linarith) (M.prob_pos i)
  rw [hi_sum_const] at key
  have e : hi_ubar M + M.β * hi_vmax M = hi_vmax M := by
    unfold hi_vmax; field_simp; ring
  linarith

/-- The set of principal's values of contracts feasible at `v`. -/
def hi_vals (M : HIModel) (f : ℝ → ℝ) (v : ℝ) : Set ℝ :=
  {x | ∃ c w, hi_Feasible M v c w ∧ hi_principalValue M f c w = x}

/-- Miao, (22.23), p. 789: the Bellman operator `(Tf)(v) = sup Σ πᵢ[−cᵢ + β f(wᵢ)]` over the
contracts satisfying (22.24)–(22.25). -/
noncomputable def hi_T (M : HIModel) (f : ℝ → ℝ) (v : ℝ) : ℝ := sSup (hi_vals M f v)

/-- Miao, p. 789: the constant contract `cᵢ = b(v)`, `wᵢ = v` is incentive compatible and
delivers the promised utility `v`. -/
theorem hi_const_feasible (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    hi_Feasible M v (fun _ => hi_b M v) (fun _ => v) := by
  refine ⟨fun i j => by unfold hi_C; simp, ?_, fun _ => hv⟩
  unfold hi_agentValue
  have := hi_b_spec M hv
  unfold hi_Bfun at this
  simp only [mul_add, Finset.sum_add_distrib, this, hi_sum_const]
  ring

/-- The principal's value of the constant contract is `−b(v) + β f(v)`. -/
theorem hi_const_value (M : HIModel) (f : ℝ → ℝ) (v : ℝ) :
    hi_principalValue M f (fun _ => hi_b M v) (fun _ => v) = -hi_b M v + M.β * f v := by
  unfold hi_principalValue; exact hi_sum_const M _

/-- Miao, p. 789: a feasible contract never gives the principal more than the first-best bound
`U(v)`, when the continuation is below `U` (Jensen's inequality for `u`). -/
theorem hi_principal_le_U (M : HIModel) {f : ℝ → ℝ} (hf : ∀ w < hi_vmax M, f w ≤ hi_U M w)
    {v : ℝ} {c w : Fin (M.N + 1) → ℝ} (h : hi_Feasible M v c w) :
    hi_principalValue M f c w ≤ hi_U M v := by
  obtain ⟨-, hpk, hw⟩ := h
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hv : v < hi_vmax M := hpk ▸ hi_agentValue_lt_vmax M hw
  set y : Fin (M.N + 1) → ℝ := fun i => hi_cstar M (w i) with hydef
  have hy : ∀ i, M.u (y i) = (1 - M.β) * w i := fun i => hi_cstar_spec M (hw i)
  set z : Fin (M.N + 1) → ℝ := fun i => (1 - M.β) * (M.θ i + c i) + M.β * y i with hzdef
  -- two-point concavity
  have hA : ∀ i, (1 - M.β) * M.u (M.θ i + c i) + M.β * M.u (y i) ≤ M.u (z i) := fun i => by
    have := M.u_strictConcave.concaveOn.2 (Set.mem_univ (M.θ i + c i)) (Set.mem_univ (y i))
      h1.le M.β_pos.le (by ring)
    simpa only [smul_eq_mul] using this
  -- Jensen
  have hB := M.u_strictConcave.concaveOn.le_map_sum (t := Finset.univ) (w := M.prob)
    (p := z) (fun i _ => (M.prob_pos i).le) M.prob_sum (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hB
  have hC : (1 - M.β) * v ≤ ∑ i, M.prob i * M.u (z i) := by
    rw [← hpk]
    unfold hi_agentValue
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_left (hA i) (M.prob_pos i).le
    rw [hy i] at this
    nlinarith
  have hD : hi_cstar M v ≤ ∑ i, M.prob i * z i := by
    rw [← M.u_strictMono.le_iff_le, hi_cstar_spec M hv]
    linarith
  -- the principal's value against `U`
  have hE : hi_principalValue M f c w ≤ ∑ i, M.prob i * (-c i + M.β * hi_U M (w i)) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (by nlinarith [hf (w i) (hw i), M.β_pos]) (M.prob_pos i).le
  have hF : (1 - M.β) * ∑ i, M.prob i * (-c i + M.β * hi_U M (w i)) =
      hi_θbar M - ∑ i, M.prob i * z i := by
    unfold hi_θbar
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have e : ∀ i, (1 - M.β) * (M.prob i * (-c i + M.β * hi_U M (w i))) =
        M.prob i * M.θ i - M.prob i * z i + M.β * (M.prob i * (hi_θbar M - M.θ i)) := by
      intro i
      simp only [hzdef, hydef, hi_U]
      field_simp
      ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    have : ∑ i, M.prob i * (hi_θbar M - M.θ i) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, hi_sum_const, hi_θbar]
      ring
    rw [this, mul_zero, add_zero]
  have hG : hi_U M v = (hi_θbar M - hi_cstar M v) / (1 - M.β) := rfl
  rw [hG, le_div_iff₀ h1]
  have := mul_le_mul_of_nonneg_left hE h1.le
  linarith

/-- The set of values is nonempty on `(−∞, vmax)`. -/
theorem hi_vals_nonempty (M : HIModel) (f : ℝ → ℝ) {v : ℝ} (hv : v < hi_vmax M) :
    (hi_vals M f v).Nonempty :=
  ⟨_, _, _, hi_const_feasible M hv, rfl⟩

/-- The set of values is bounded above by `U(v)` when `f ≤ U`. -/
theorem hi_vals_bddAbove (M : HIModel) {f : ℝ → ℝ} (hf : ∀ w < hi_vmax M, f w ≤ hi_U M w)
    (v : ℝ) : BddAbove (hi_vals M f v) :=
  ⟨hi_U M v, by rintro _ ⟨c, w, h, rfl⟩; exact hi_principal_le_U M hf h⟩

/-- The value of any feasible contract is at most `Tf(v)`. -/
theorem hi_le_T (M : HIModel) {f : ℝ → ℝ} (hf : ∀ w < hi_vmax M, f w ≤ hi_U M w) {v : ℝ}
    {c w : Fin (M.N + 1) → ℝ} (h : hi_Feasible M v c w) :
    hi_principalValue M f c w ≤ hi_T M f v :=
  le_csSup (hi_vals_bddAbove M hf v) ⟨c, w, h, rfl⟩

/-- **(22.26)** (Miao, p. 789). `T` maps the space `F` of functions between the bounds into
itself: `−b(v)/(1 − β) ≤ Tf(v) ≤ Σ πᵢ [θᵢ − c*(v)]/(1 − β)`. -/
theorem eq_22_26 (M : HIModel) {f : ℝ → ℝ} (hf : hi_InF M f) : hi_InF M (hi_T M f) := by
  intro v hv
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  constructor
  · have := hi_le_T M (fun w hw => (hf w hw).2) (hi_const_feasible M hv)
    rw [hi_const_value] at this
    have hL := (hf v hv).1
    unfold hi_L at hL ⊢
    have e : -hi_b M v / (1 - M.β) = -hi_b M v + M.β * (-hi_b M v / (1 - M.β)) := by
      field_simp; ring
    rw [e]
    nlinarith [M.β_pos]
  · exact csSup_le (hi_vals_nonempty M f hv) (by
      rintro _ ⟨c, w, h, rfl⟩; exact hi_principal_le_U M (fun w hw => (hf w hw).2) h)

/-- Blackwell's monotonicity and discounting (Miao, p. 792): if `f ≤ g + ε` on `(−∞, vmax)`,
then `Tf ≤ Tg + βε`. -/
theorem hi_T_le_add (M : HIModel) {f g : ℝ → ℝ} (hg : hi_InF M g) {ε : ℝ}
    (hfg : ∀ w < hi_vmax M, f w ≤ g w + ε) {v : ℝ} (hv : v < hi_vmax M) :
    hi_T M f v ≤ hi_T M g v + M.β * ε := by
  refine csSup_le (hi_vals_nonempty M f hv) ?_
  rintro _ ⟨c, w, h, rfl⟩
  have h2 := hi_le_T M (fun w hw => (hg w hw).2) h
  have h3 : hi_principalValue M f c w ≤ hi_principalValue M g c w + M.β * ε := by
    unfold hi_principalValue
    rw [← hi_sum_const M (M.β * ε), ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have := mul_le_mul_of_nonneg_left (hfg (w i) (h.2.2 i)) M.β_pos.le
    nlinarith [M.prob_pos i]
  linarith

/-- Miao, p. 792: `T` is a contraction of modulus `β` in the sup distance on `F`. -/
theorem hi_T_abs_le (M : HIModel) {f g : ℝ → ℝ} (hf : hi_InF M f) (hg : hi_InF M g) {ε : ℝ}
    (hfg : ∀ w < hi_vmax M, |f w - g w| ≤ ε) {v : ℝ} (hv : v < hi_vmax M) :
    |hi_T M f v - hi_T M g v| ≤ M.β * ε := by
  have a := hi_T_le_add M hg (f := f) (ε := ε)
    (fun w hw => by linarith [(abs_le.1 (hfg w hw)).2]) hv
  have b := hi_T_le_add M hf (f := g) (ε := ε)
    (fun w hw => by linarith [(abs_le.1 (hfg w hw)).1]) hv
  rw [abs_le]; constructor <;> linarith

/-- Two functions in `F` are within `(θ̄ − θ₁)/(1 − β)` of each other. -/
theorem hi_InF_abs_sub (M : HIModel) {f g : ℝ → ℝ} (hf : hi_InF M f) (hg : hi_InF M g)
    {v : ℝ} (hv : v < hi_vmax M) : |f v - g v| ≤ (hi_θbar M - M.θ 0) / (1 - M.β) := by
  have := hi_U_sub_L_le M hv
  rw [abs_le]; constructor <;> linarith [hf v hv, hg v hv]

/-- The iterates `Pₖ = Tᵏ L`. -/
noncomputable def hi_Pk (M : HIModel) (k : ℕ) : ℝ → ℝ := (hi_T M)^[k] (hi_L M)

/-- The lower bound lies in `F`. -/
theorem hi_L_InF (M : HIModel) : hi_InF M (hi_L M) := by
  intro v hv
  refine ⟨le_rfl, ?_⟩
  have := hi_U_sub_L_le M hv
  have h := hi_b_le_cstar M hv
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  unfold hi_U hi_L
  rw [div_le_div_iff_of_pos_right h1]
  -- `−b ≤ θ̄ − c*`: `c* ≤ θₙ + b ≤ ...`; use `u(c*) = B(b) ≤ u(θ̄ + b)` by Jensen
  have hJ := M.u_strictConcave.concaveOn.le_map_sum (t := Finset.univ) (w := M.prob)
    (p := fun i => M.θ i + hi_b M v) (fun i _ => (M.prob_pos i).le) M.prob_sum
    (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hJ
  have hB := hi_b_spec M hv
  unfold hi_Bfun at hB
  rw [hB, ← hi_cstar_spec M hv, M.u_strictMono.le_iff_le] at hJ
  have e : ∑ i, M.prob i * (M.θ i + hi_b M v) = hi_θbar M + hi_b M v := by
    simp only [mul_add, Finset.sum_add_distrib, hi_sum_const, hi_θbar]
  linarith

/-- Every iterate lies in `F`. -/
theorem hi_Pk_InF (M : HIModel) (k : ℕ) : hi_InF M (hi_Pk M k) := by
  induction k with
  | zero => exact hi_L_InF M
  | succ k ih =>
    unfold hi_Pk at *
    rw [Function.iterate_succ_apply']
    exact eq_22_26 M ih

/-- Miao, p. 792: `|Pₖ₊₁ − Pₖ| ≤ K βᵏ` on `(−∞, vmax)`, `K = (θ̄ − θ₁)/(1 − β)`. -/
theorem hi_Pk_succ_abs (M : HIModel) (k : ℕ) {v : ℝ} (hv : v < hi_vmax M) :
    |hi_Pk M (k + 1) v - hi_Pk M k v| ≤ (hi_θbar M - M.θ 0) / (1 - M.β) * M.β ^ k := by
  induction k generalizing v with
  | zero => simpa using hi_InF_abs_sub M (hi_Pk_InF M 1) (hi_Pk_InF M 0) hv
  | succ k ih =>
    have e1 : hi_Pk M (k + 1 + 1) = hi_T M (hi_Pk M (k + 1)) := by
      unfold hi_Pk; rw [Function.iterate_succ_apply']
    have e2 : hi_Pk M (k + 1) = hi_T M (hi_Pk M k) := by
      unfold hi_Pk; rw [Function.iterate_succ_apply']
    have := hi_T_abs_le M (hi_Pk_InF M (k + 1)) (hi_Pk_InF M k) (fun w hw => ih hw) hv
    rw [← e1, ← e2] at this
    have e3 : M.β * ((hi_θbar M - M.θ 0) / (1 - M.β) * M.β ^ k) =
        (hi_θbar M - M.θ 0) / (1 - M.β) * M.β ^ (k + 1) := by ring
    linarith

/-- Miao, p. 792: the iterates converge on `(−∞, vmax)`. -/
theorem hi_Pk_cauchy (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    CauchySeq fun k => hi_Pk M k v :=
  cauchySeq_of_le_geometric M.β _ M.β_lt_one fun k => by
    rw [Real.dist_eq, abs_sub_comm]; exact hi_Pk_succ_abs M k hv

/-- The value function `P = lim Tᵏ L`. -/
noncomputable def hi_P (M : HIModel) (v : ℝ) : ℝ := limUnder atTop fun k => hi_Pk M k v

/-- `Pₖ(v) → P(v)` on `(−∞, vmax)`. -/
theorem hi_Pk_tendsto (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) :
    Tendsto (fun k => hi_Pk M k v) atTop (𝓝 (hi_P M v)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hi_Pk_cauchy M hv))

/-- `|P − Pₖ| ≤ K βᵏ / (1 − β)`. -/
theorem hi_P_abs_sub (M : HIModel) (k : ℕ) {v : ℝ} (hv : v < hi_vmax M) :
    |hi_Pk M k v - hi_P M v| ≤ (hi_θbar M - M.θ 0) / (1 - M.β) * M.β ^ k / (1 - M.β) := by
  rw [← Real.dist_eq]
  exact dist_le_of_le_geometric_of_tendsto M.β _ M.β_lt_one
    (fun k => by rw [Real.dist_eq, abs_sub_comm]; exact hi_Pk_succ_abs M k hv)
    (hi_Pk_tendsto M hv) k

/-- `P` lies in `F`. -/
theorem hi_P_InF (M : HIModel) : hi_InF M (hi_P M) := fun v hv =>
  ⟨ge_of_tendsto' (hi_Pk_tendsto M hv) fun k => (hi_Pk_InF M k v hv).1,
    le_of_tendsto' (hi_Pk_tendsto M hv) fun k => (hi_Pk_InF M k v hv).2⟩

/-- `P` is a fixed point of `T` on `(−∞, vmax)`: the Bellman equation (22.23). -/
theorem hi_P_fixed (M : HIModel) {v : ℝ} (hv : v < hi_vmax M) : hi_T M (hi_P M) v = hi_P M v := by
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  set K := (hi_θbar M - M.θ 0) / (1 - M.β)
  have hlim : Tendsto (fun k => hi_Pk M (k + 1) v) atTop (𝓝 (hi_T M (hi_P M) v)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hb : ∀ k, dist (hi_Pk M (k + 1) v) (hi_T M (hi_P M) v) ≤
        M.β * (K * M.β ^ k / (1 - M.β)) := fun k => by
      have e : hi_Pk M (k + 1) = hi_T M (hi_Pk M k) := by
        unfold hi_Pk; rw [Function.iterate_succ_apply']
      rw [e, Real.dist_eq]
      exact hi_T_abs_le M (hi_Pk_InF M k) (hi_P_InF M) (fun w hw => hi_P_abs_sub M k hw) hv
    refine squeeze_zero (fun _ => dist_nonneg) hb ?_
    have : Tendsto (fun k => M.β * (K * M.β ^ k / (1 - M.β))) atTop
        (𝓝 (M.β * (K * 0 / (1 - M.β)))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one M.β_pos.le M.β_lt_one).const_mul K |>.div_const
        _).const_mul _
    simpa using this
  exact tendsto_nhds_unique hlim ((hi_Pk_tendsto M hv).comp (tendsto_add_atTop_nat 1))

/-- Uniqueness: two fixed points of `T` in `F` agree on `(−∞, vmax)`. -/
theorem hi_fixed_unique (M : HIModel) {P Q : ℝ → ℝ} (hP : hi_InF M P) (hQ : hi_InF M Q)
    (hPf : ∀ v < hi_vmax M, hi_T M P v = P v) (hQf : ∀ v < hi_vmax M, hi_T M Q v = Q v)
    {v : ℝ} (hv : v < hi_vmax M) : P v = Q v := by
  set K := (hi_θbar M - M.θ 0) / (1 - M.β)
  have key : ∀ k : ℕ, ∀ w < hi_vmax M, |P w - Q w| ≤ K * M.β ^ k := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hi_InF_abs_sub M hP hQ hw
    | succ k ih =>
      intro w hw
      have := hi_T_abs_le M hP hQ ih hw
      rw [hPf w hw, hQf w hw] at this
      calc _ ≤ _ := this
        _ = _ := by ring
  have hlim : Tendsto (fun k => K * M.β ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one M.β_pos.le M.β_lt_one).const_mul K
  have h0 : |P v - Q v| ≤ 0 := ge_of_tendsto' hlim fun k => key k v hv
  have := abs_nonpos_iff.1 h0
  linarith

/-- `b(v)` is increasing on `(−∞, vmax)`. -/
theorem hi_b_mono (M : HIModel) {v v' : ℝ} (hv' : v' < hi_vmax M) (hvv : v ≤ v') :
    hi_b M v ≤ hi_b M v' := by
  have hv : v < hi_vmax M := lt_of_le_of_lt hvv hv'
  rw [← (hi_Bfun_strictMono M).le_iff_le, hi_b_spec M hv, hi_b_spec M hv']
  exact mul_le_mul_of_nonneg_left hvv (by linarith [M.β_lt_one])

/-- The lower bound `L` is decreasing. -/
theorem hi_L_antitoneOn (M : HIModel) : AntitoneOn (hi_L M) (Set.Iio (hi_vmax M)) := by
  intro v _ v' hv' hvv
  have := hi_b_mono M hv' hvv
  have h1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  unfold hi_L
  exact div_le_div_of_nonneg_right (by linarith) h1.le

/-- Miao, p. 792: "`T` maps a decreasing function to a decreasing function". Given a contract
feasible at `v'`, lowering every `wᵢ` by `(v' − v)/β` gives a contract feasible at `v ≤ v'`
that is at least as good for the principal. -/
theorem hi_T_antitoneOn (M : HIModel) {f : ℝ → ℝ} (hf : hi_InF M f)
    (hfa : AntitoneOn f (Set.Iio (hi_vmax M))) : AntitoneOn (hi_T M f) (Set.Iio (hi_vmax M)) := by
  intro v hv v' hv' hvv
  refine csSup_le (hi_vals_nonempty M f hv') ?_
  rintro _ ⟨c, w, ⟨hic, hpk, hw⟩, rfl⟩
  set k := -((v' - v) / M.β)
  have hk : k ≤ 0 := by
    have : 0 ≤ (v' - v) / M.β := div_nonneg (by linarith) M.β_pos.le
    linarith
  have hfeas : hi_Feasible M v c (fun l => w l + k) := by
    refine ⟨fun i j => by rw [hi_C_shift]; exact hic i j, ?_, fun i => by linarith [hw i]⟩
    rw [hi_agentValue_shift, hpk]
    have : M.β * k = -(v' - v) := by
      simp only [k]; rw [mul_neg, mul_div_cancel₀ _ M.β_pos.ne']
    linarith
  refine le_trans ?_ (hi_le_T M (fun w hw => (hf w hw).2) hfeas)
  unfold hi_principalValue
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (M.prob_pos i).le
  have := hfa (show w i + k ∈ Set.Iio (hi_vmax M) by
    simp only [Set.mem_Iio]; linarith [hw i]) (hw i) (by linarith)
  nlinarith [M.β_pos]

/-- The iterates are decreasing. -/
theorem hi_Pk_antitoneOn (M : HIModel) (k : ℕ) :
    AntitoneOn (hi_Pk M k) (Set.Iio (hi_vmax M)) := by
  induction k with
  | zero => exact hi_L_antitoneOn M
  | succ k ih =>
    have e : hi_Pk M (k + 1) = hi_T M (hi_Pk M k) := by
      unfold hi_Pk; rw [Function.iterate_succ_apply']
    rw [e]
    exact hi_T_antitoneOn M (hi_Pk_InF M k) ih

/-- **Proposition 22.3.1** (Miao, p. 791), the contraction part. There is a function `P` in the
space `F` of functions lying between the bounds (22.26) that solves the Bellman equation
(22.23) on `(−∞, vmax)`; any other solution in `F` agrees with it on `(−∞, vmax)`; and `P` is
decreasing. (Concavity is `proposition_22_3_1_concave`; strict concavity, continuous
differentiability and the uniqueness of the policies are not proved; see
`docs/HI-corrections.md`.) -/
theorem proposition_22_3_1 (M : HIModel) :
    ∃ P : ℝ → ℝ, hi_InF M P ∧ (∀ v < hi_vmax M, hi_T M P v = P v) ∧
      (∀ Q : ℝ → ℝ, hi_InF M Q → (∀ v < hi_vmax M, hi_T M Q v = Q v) →
        ∀ v < hi_vmax M, Q v = P v) ∧ AntitoneOn P (Set.Iio (hi_vmax M)) := by
  refine ⟨hi_P M, hi_P_InF M, fun v hv => hi_P_fixed M hv, fun Q hQ hQf v hv =>
    hi_fixed_unique M hQ (hi_P_InF M) hQf (fun w hw => hi_P_fixed M hw) hv, ?_⟩
  intro v hv v' hv' hvv
  exact le_of_tendsto_of_tendsto' (hi_Pk_tendsto M hv') (hi_Pk_tendsto M hv)
    fun k => hi_Pk_antitoneOn M k hv hv' hvv

/-- Miao, p. 793: "`P(v) = lim Pₖ(v)` is concave": a pointwise limit of concave functions is
concave. -/
theorem hi_concaveOn_of_tendsto {s : Set ℝ} {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ}
    (hF : ∀ k, ConcaveOn ℝ s (F k)) (hG : ∀ x ∈ s, Tendsto (fun k => F k x) atTop (𝓝 (G x))) :
    ConcaveOn ℝ s G := by
  refine ⟨(hF 0).1, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy : a • x + b • y ∈ s := (hF 0).1 hx hy ha hb hab
  simp only [smul_eq_mul] at hxy ⊢
  exact le_of_tendsto_of_tendsto' (((hG x hx).const_mul a).add ((hG y hy).const_mul b))
    (hG _ hxy) fun k => by simpa only [smul_eq_mul] using (hF k).2 hx hy ha hb hab

end Miao.RecursiveContracts
