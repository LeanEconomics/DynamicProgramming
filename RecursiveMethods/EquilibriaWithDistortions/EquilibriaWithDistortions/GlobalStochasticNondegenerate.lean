/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import EquilibriaWithDistortions.GlobalStochasticEquilibrium

/-!
# A non-degenerate stochastic equilibrium for any finite set of technologies (SLP p. 560)

On p. 560 the book says that, in the stochastic case (§18.3 (8)–(9), pp. 558–560), existence of
an equilibrium "follows from Schauder's Theorem". `GlobalStochastic.Ts_psi` shows that this
argument yields only the degenerate fixed point `ψ` (zero consumption forever), and
`GlobalStochasticEquilibrium` proves a non-degenerate equilibrium only when all states share one
technology. This module proves existence for **any** finite set of technologies satisfying the
per-shock assumptions, with no extra hypothesis: the least fixed point `lfp = lim Tⁿ0` always has
positive consumption.

The proof compares the equilibrium with an **auxiliary planner** whose technology in state `j` is
`Φ_j(k) = θ f_j(0) + (1 − θ) f_j(k)`. Unlike `ψ_j`, `Φ_j` is concave, and `Φ_j ≤ ψ_j` with
`Φ_j(b) − Φ_j(a) > (1 − θ)(b − a) f′_j(b)`. The planner's problem
`V_j(k) = max_{0 ≤ z ≤ Φ_j(k)} U(Φ_j(k) − z) + β Σ_l π_jl V_l(z)` has a concave value function,
its consumption `c_j(k)` is positive (Inada condition), and raising saving by `δ` gives the
Euler inequality with the agent's after-tax return, `U′(c_j(k)) ≥ β(1 − θ) Σ_l π_jl f′_l(z)
U′(c_l(z))`. Then `{h ∈ F : ψ − h ≥ c}` is invariant under `T` and contains `0`, so every iterate
`Tⁿ0`, and the limit `lfp`, leaves consumption at least `c > 0`.

* The planner: `Phi` and its properties (`Phi_le_psi`, `Phi_sub_gt`, `Phi_concave`); the Bellman
  operator `plBellOp` (a `β`-contraction, `plBellOp_contracting`) and its fixed point `Vstar`,
  which is concave (`isConc_Vstar`); an optimal saving `pz` (`pz_spec`), with consumption `pc`.
* `pc_pos`: the planner's consumption is positive.
* `pc_euler`: the planner's Euler inequality with the agent's return `β(1 − θ) f′`.
* `IsInFs.Ts_floor`, `Tsit_floor`, `lfp_floor`: the planner's consumption is a floor for the
  consumption of every `Tⁿ0` and of `lfp`.
* `lfp_lt_psi`, `exists_nondegenerate_super`: `lfp` has positive consumption everywhere, so the
  hypothesis of `StochModel.lfp_equilibrium_of_super` always holds.
* `exists_nondegenerate_equilibrium_KT`: with no cross-state condition, `lfp` solves (9) in
  Kuhn–Tucker form with positive consumptions today and tomorrow.
* `exists_nondegenerate_equilibrium`: under `CrossState`, `lfp` solves (9) as an equation.
* `crossState_of_persistent`: `β(1 − θ) π_ii f′_i(0) > 1` for every `i` implies `CrossState`.
* Examples: `stochJ_nondegenerate` (the model in which Exercise 18.8 fails still has a
  non-degenerate equilibrium) and `stochP_equilibrium` (two different technologies, `modelHigh`
  and `modelE`, with persistent shocks; `stochP_tech_ne`, `stochP_crossState`).

**Correction (p. 560).** Existence of a non-degenerate equilibrium is true for every finite set of
technologies, but not by the book's argument: Schauder's Theorem on `F` gives `ψ`
(`StochModel.Ts_psi`). It follows from monotone iteration from `0` (Theorem 17.7 from the least
element) together with the planner's consumption floor `lfp_floor`. No anchor at a steady state,
no closeness of technologies and no extra Inada condition on `f′` are needed.
-/

namespace StokeyLucasPrescott.EquilibriaWithDistortions

open Set Filter Topology BoundedContinuousFunction

namespace StochModel

variable {ι : Type} [Fintype ι] (S : StochModel ι)

/-- `0 < β < 1` for the common discount factor. -/
theorem β_pos' : 0 < S.β := by
  obtain ⟨j, -⟩ := S.B_eq
  rw [← S.tech_β j]; exact (S.tech j).β_pos

/-- `β < 1` for the common discount factor. -/
theorem β_lt_one' : S.β < 1 := by
  obtain ⟨j, -⟩ := S.B_eq
  rw [← S.tech_β j]; exact (S.tech j).β_lt_one

/-- `0 < θ < 1` for the common tax rate. -/
theorem θ_mem : 0 < S.θ ∧ S.θ < 1 := by
  obtain ⟨j, -⟩ := S.B_eq
  rw [← S.tech_θ j]; exact ⟨(S.tech j).θ_pos, (S.tech j).θ_lt_one⟩

/-- The common utility is continuous on `[0, ∞)`. -/
theorem U_cont : ContinuousOn S.U (Ici 0) := by
  obtain ⟨j, -⟩ := S.B_eq
  rw [← S.tech_U j]; exact (S.tech j).U_cont

/-- The common utility is strictly increasing on `[0, ∞)`. -/
theorem U_strictMono : StrictMonoOn S.U (Ici 0) := by
  obtain ⟨j, -⟩ := S.B_eq
  rw [← S.tech_U j]; exact (S.tech j).U_strictMono

/-- The common utility is strictly concave on `[0, ∞)`. -/
theorem U_strictConcave : StrictConcaveOn ℝ (Ici 0) S.U := by
  obtain ⟨j, -⟩ := S.B_eq
  rw [← S.tech_U j]; exact (S.tech j).U_strictConcave

/-- `U′` is the derivative of the common utility on `(0, ∞)`. -/
theorem U_deriv {c : ℝ} (hc : 0 < c) : HasDerivAt S.U (S.U' c) c := by
  obtain ⟨j, -⟩ := S.B_eq
  rw [← S.tech_U j, ← S.tech_U' j]; exact (S.tech j).U_deriv c hc

/-! ### The auxiliary planner's technology `Φ_j(k) = θ f_j(0) + (1 − θ) f_j(k)` -/

/-- The technology of the auxiliary planner: `Φ_j(k) = θ f_j(0) + (1 − θ) f_j(k)`. -/
noncomputable def Phi (j : ι) (k : ℝ) : ℝ := S.θ * (S.tech j).f 0 + (1 - S.θ) * (S.tech j).f k

/-- `Φ_j ≤ ψ_j` on `[0, ∞)`: the gap is `θ [f_j(k) − f_j(0) − k f′_j(k)] ≥ 0`. -/
theorem Phi_le_psi (j : ι) {k : ℝ} (hk : 0 ≤ k) : S.Phi j k ≤ (S.tech j).psi k := by
  have hθ := S.tech_θ j
  have e : (S.tech j).psi k - S.Phi j k =
      S.θ * ((S.tech j).f k - (S.tech j).f 0 - k * (S.tech j).f' k) := by
    simp only [GlobalModel.psi, Phi, hθ]; ring
  rcases hk.eq_or_lt with h0 | hpos
  · rw [← h0] at e ⊢
    have : (S.tech j).psi 0 - S.Phi j 0 = 0 := by rw [e]; ring
    linarith
  · have h1 := (S.tech j).f'_mul_lt_sub le_rfl hpos
    have : 0 ≤ (S.tech j).psi k - S.Phi j k := by
      rw [e]; exact mul_nonneg S.θ_mem.1.le (by linarith)
    linarith

/-- `Φ_j(b) − Φ_j(a) > (1 − θ)(b − a) f′_j(b)` for `0 ≤ a < b`. -/
theorem Phi_sub_gt (j : ι) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (1 - S.θ) * (b - a) * (S.tech j).f' b < S.Phi j b - S.Phi j a := by
  have h1 := (S.tech j).f'_mul_lt_sub ha hab
  have h2 : 0 < 1 - S.θ := by linarith [S.θ_mem.2]
  have : S.Phi j b - S.Phi j a = (1 - S.θ) * ((S.tech j).f b - (S.tech j).f a) := by
    simp only [Phi]; ring
  rw [this, mul_assoc]
  exact mul_lt_mul_of_pos_left (by linarith) h2

/-- `Φ_j` is strictly increasing on `[0, ∞)`. -/
theorem Phi_lt (j : ι) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : S.Phi j a < S.Phi j b := by
  have h := S.Phi_sub_gt j ha hab
  have : 0 < (1 - S.θ) * (b - a) * (S.tech j).f' b :=
    mul_pos (mul_pos (by linarith [S.θ_mem.2]) (by linarith))
      ((S.tech j).f'_pos (ha.trans hab.le))
  linarith

/-- `Φ_j` is nondecreasing on `[0, ∞)`. -/
theorem Phi_le (j : ι) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : S.Phi j a ≤ S.Phi j b := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · exact (S.Phi_lt j ha h).le

/-- `Φ_j(k) ≥ Φ_j(0) = f_j(0) > 0`. -/
theorem Phi_pos (j : ι) {k : ℝ} (hk : 0 ≤ k) : 0 < S.Phi j k := by
  have h0 : S.Phi j 0 = (S.tech j).f 0 := by simp only [Phi]; ring
  have := S.Phi_le j le_rfl hk
  linarith [(S.tech j).f_zero_pos]

/-- `Φ_j` is continuous on `[0, ∞)`. -/
theorem Phi_continuousOn (j : ι) : ContinuousOn (S.Phi j) (Ici 0) :=
  continuousOn_const.add (continuousOn_const.mul (S.tech j).f_cont)

/-- `Φ_j` is concave on `[0, ∞)` (it is affine in the concave `f_j`). -/
theorem Phi_concave (j : ι) : ConcaveOn ℝ (Ici 0) (S.Phi j) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have hf := (S.tech j).f_strictConcave.concaveOn.2 hx hy ha hb hab
  have h2 : 0 ≤ 1 - S.θ := by linarith [S.θ_mem.2]
  simp only [smul_eq_mul] at hf ⊢
  simp only [Phi]
  have := mul_le_mul_of_nonneg_left hf h2
  have e : a * (S.θ * (S.tech j).f 0 + (1 - S.θ) * (S.tech j).f x) +
      b * (S.θ * (S.tech j).f 0 + (1 - S.θ) * (S.tech j).f y) =
      (a + b) * (S.θ * (S.tech j).f 0) +
        (1 - S.θ) * (a * (S.tech j).f x + b * (S.tech j).f y) := by ring
  rw [e, hab, one_mul]
  linarith

/-- `Φ_j` maps `K = [0, B]` into `(0, B]`. -/
theorem Phi_le_B (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) : S.Phi j k ≤ S.B :=
  (S.Phi_le_psi j hk.1).trans (S.psi_le_B j hk)

/-! ### The auxiliary planner's Bellman equation -/

/-- The space of value functions of the auxiliary planner: one bounded continuous function on
`K = [0, B]` for each state. -/
abbrev VSpace := ι → (Icc (0 : ℝ) S.B →ᵇ ℝ)

/-- A value function of state `l`, extended to `ℝ` (constant outside `K`). -/
noncomputable def vE (V : S.VSpace) (l : ι) (z : ℝ) : ℝ := IccExtend S.B_pos.le (V l) z

/-- `vE V l` is continuous. -/
theorem vE_continuous (V : S.VSpace) (l : ι) : Continuous (S.vE V l) :=
  (V l).continuous.Icc_extend'

/-- `|V_l(z)| ≤ ‖V‖`. -/
theorem abs_vE_le (V : S.VSpace) (l : ι) (z : ℝ) : |S.vE V l z| ≤ ‖V‖ :=
  ((V l).norm_coe_le_norm _).trans (norm_le_pi_norm V l)

/-- `|V_l(z) − W_l(z)| ≤ d(V, W)`. -/
theorem abs_vE_sub_le (V W : S.VSpace) (l : ι) (z : ℝ) :
    |S.vE V l z - S.vE W l z| ≤ dist V W := by
  have h1 := (V l).dist_coe_le_dist (g := W l) (projIcc 0 S.B S.B_pos.le z)
  rw [Real.dist_eq] at h1
  exact h1.trans (dist_le_pi_dist V W l)

/-- The planner's objective at `(k, ξ_j)` when saving `z`:
`U(Φ_j(k) − z) + β Σ_l π_jl V_l(z)`. -/
noncomputable def obj (V : S.VSpace) (j : ι) (k z : ℝ) : ℝ :=
  S.U (S.Phi j k - z) + S.β * ∑ l, S.π j l * S.vE V l z

/-- The clamp of `t` to `[0, 1]`. -/
noncomputable def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

/-- `clamp01` is the identity on `[0, 1]`. -/
theorem clamp01_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp01 t = t := by
  simp only [clamp01, min_eq_right ht.2, max_eq_right ht.1]

/-- `0 ≤ clamp01 t ≤ 1`. -/
theorem clamp01_mem (t : ℝ) : clamp01 t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- The **Bellman operator** of the auxiliary planner, pointwise:
`(PV)_j(k) = max_{0 ≤ z ≤ Φ_j(k)} U(Φ_j(k) − z) + β Σ_l π_jl V_l(z)`, with `z = t Φ_j(k)`,
`t ∈ [0, 1]`. -/
noncomputable def plBell (V : S.VSpace) (j : ι) (k : ℝ) : ℝ :=
  sSup ((fun t => S.obj V j k (clamp01 t * S.Phi j k)) '' Icc 0 1)

/-- The objective is jointly continuous in `(k, t) ∈ K × ℝ`. -/
theorem obj_continuous (V : S.VSpace) (j : ι) :
    Continuous fun p : Icc (0 : ℝ) S.B × ℝ => S.obj V j p.1 (clamp01 p.2 * S.Phi j p.1) := by
  have hP : Continuous fun p : Icc (0 : ℝ) S.B × ℝ => S.Phi j p.1 :=
    (S.Phi_continuousOn j).comp_continuous (continuous_subtype_val.comp continuous_fst)
      fun p => mem_Ici.2 p.1.2.1
  have hc : Continuous clamp01 := continuous_const.max (continuous_const.min continuous_id)
  have hz : Continuous fun p : Icc (0 : ℝ) S.B × ℝ => clamp01 p.2 * S.Phi j p.1 :=
    (hc.comp continuous_snd).mul hP
  refine Continuous.add ?_ (continuous_const.mul (continuous_finsetSum _ fun l _ =>
    continuous_const.mul ((S.vE_continuous V l).comp hz)))
  refine S.U_cont.comp_continuous (hP.sub hz) fun p => mem_Ici.2 ?_
  have h1 := (clamp01_mem p.2).2
  have h2 := S.Phi_pos j p.1.2.1
  nlinarith

/-- `(PV)_j` is continuous on `K`. -/
theorem plBell_continuous (V : S.VSpace) (j : ι) :
    Continuous fun k : Icc (0 : ℝ) S.B => S.plBell V j k :=
  isCompact_Icc.continuous_sSup (S.obj_continuous V j)

/-- **The Bellman operator** `P` on `VSpace`. -/
noncomputable def plBellOp (V : S.VSpace) : S.VSpace := fun j =>
  BoundedContinuousFunction.mkOfCompact ⟨fun k => S.plBell V j k, S.plBell_continuous V j⟩

/-- The values of the objective over `t ∈ [0, 1]` form a compact set. -/
theorem obj_image_isCompact (V : S.VSpace) (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    IsCompact ((fun t => S.obj V j k (clamp01 t * S.Phi j k)) '' Icc 0 1) :=
  isCompact_Icc.image ((S.obj_continuous V j).comp
    (Continuous.prodMk_right (Y := ℝ) (⟨k, hk⟩ : Icc (0 : ℝ) S.B)) :)

/-- Every feasible saving `z ∈ [0, Φ_j(k)]` gives at most `(PV)_j(k)`. -/
theorem obj_le_plBell (V : S.VSpace) (j : ι) {k z : ℝ} (hk : k ∈ Icc 0 S.B)
    (hz : z ∈ Icc 0 (S.Phi j k)) : S.obj V j k z ≤ S.plBell V j k := by
  have hP := S.Phi_pos j hk.1
  refine le_csSup (S.obj_image_isCompact V j hk).bddAbove ⟨z / S.Phi j k,
    ⟨div_nonneg hz.1 hP.le, div_le_one_of_le₀ hz.2 hP.le⟩, ?_⟩
  simp only
  rw [clamp01_of_mem ⟨div_nonneg hz.1 hP.le, div_le_one_of_le₀ hz.2 hP.le⟩,
    div_mul_cancel₀ _ hP.ne']

/-- The maximum in `(PV)_j(k)` is attained. -/
theorem exists_plBell_eq (V : S.VSpace) (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    ∃ z ∈ Icc 0 (S.Phi j k), S.obj V j k z = S.plBell V j k := by
  obtain ⟨t, ht, hteq⟩ := (S.obj_image_isCompact V j hk).sSup_mem
    ((nonempty_Icc.2 zero_le_one).image _)
  have hP := S.Phi_pos j hk.1
  refine ⟨clamp01 t * S.Phi j k, ⟨mul_nonneg (clamp01_mem t).1 hP.le,
    mul_le_of_le_one_left hP.le (clamp01_mem t).2⟩, hteq⟩

/-- `(PV)_j(k) ≤ c` when every feasible saving gives at most `c`. -/
theorem plBell_le (V : S.VSpace) (j : ι) {k c : ℝ} (hk : k ∈ Icc 0 S.B)
    (h : ∀ z ∈ Icc 0 (S.Phi j k), S.obj V j k z ≤ c) : S.plBell V j k ≤ c := by
  have hP := S.Phi_pos j hk.1
  refine csSup_le ((nonempty_Icc.2 zero_le_one).image _) (forall_mem_image.2 fun t _ => ?_)
  exact h _ ⟨mul_nonneg (clamp01_mem t).1 hP.le, mul_le_of_le_one_left hP.le (clamp01_mem t).2⟩

/-- The objective moves by at most `β d(V, W)`. -/
theorem obj_le_obj_add (V W : S.VSpace) (j : ι) (k z : ℝ) :
    S.obj V j k z ≤ S.obj W j k z + S.β * dist V W := by
  have h1 : ∑ l, S.π j l * S.vE V l z ≤ ∑ l, S.π j l * (S.vE W l z + dist V W) :=
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
      (by linarith [(abs_le.1 (S.abs_vE_sub_le V W l z)).2]) (S.π_nonneg j l)
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, S.π_sum, one_mul] at h1
  have := mul_le_mul_of_nonneg_left h1 S.β_pos'.le
  simp only [obj]
  linarith

/-- `P` is a contraction with modulus `β`. -/
theorem dist_plBellOp_le (V W : S.VSpace) :
    dist (S.plBellOp V) (S.plBellOp W) ≤ S.β * dist V W := by
  have h0 : 0 ≤ S.β * dist V W := mul_nonneg S.β_pos'.le dist_nonneg
  refine (dist_pi_le_iff h0).2 fun j => (BoundedContinuousFunction.dist_le h0).2 fun k => ?_
  have h1 : S.plBell V j k ≤ S.plBell W j k + S.β * dist V W :=
    S.plBell_le V j k.2 fun z hz => (S.obj_le_obj_add V W j k z).trans
      (add_le_add_left (S.obj_le_plBell W j k.2 hz) _)
  have h2 : S.plBell W j k ≤ S.plBell V j k + S.β * dist V W := by
    rw [dist_comm]
    exact S.plBell_le W j k.2 fun z hz => (S.obj_le_obj_add W V j k z).trans
      (add_le_add_left (S.obj_le_plBell V j k.2 hz) _)
  rw [Real.dist_eq, abs_le]
  change -(S.β * dist V W) ≤ S.plBell V j k - S.plBell W j k ∧
    S.plBell V j k - S.plBell W j k ≤ S.β * dist V W
  constructor <;> linarith

/-- `P` is a contracting map. -/
theorem plBellOp_contracting : ContractingWith ⟨S.β, S.β_pos'.le⟩ S.plBellOp :=
  ⟨NNReal.coe_lt_coe.1 (by rw [NNReal.coe_one]; exact S.β_lt_one'),
    LipschitzWith.of_dist_le_mul fun V W => S.dist_plBellOp_le V W⟩

/-- **The planner's value function**: the fixed point of `P`. -/
noncomputable def Vstar : S.VSpace :=
  ContractingWith.fixedPoint S.plBellOp S.plBellOp_contracting

/-- The Bellman equation `V*_j(k) = (PV*)_j(k)` on `K`. -/
theorem vE_Vstar (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.vE S.Vstar j k = S.plBell S.Vstar j k := by
  have h : S.plBellOp S.Vstar = S.Vstar := S.plBellOp_contracting.fixedPoint_isFixedPt
  calc S.vE S.Vstar j k = S.Vstar j ⟨k, hk⟩ := IccExtend_of_mem _ _ hk
    _ = S.plBellOp S.Vstar j ⟨k, hk⟩ := by rw [h]
    _ = S.plBell S.Vstar j k := rfl

/-! ### Concavity of the planner's value function -/

/-- Every state's value function is concave on `K`. -/
def IsConc (V : S.VSpace) : Prop := ∀ l, ConcaveOn ℝ (Icc 0 S.B) (S.vE V l)

/-- The zero value function is concave. -/
theorem isConc_zero : S.IsConc 0 := fun l => by
  have : S.vE 0 l = fun _ => 0 := rfl
  rw [this]
  exact concaveOn_const 0 (convex_Icc 0 S.B)

/-- `P` preserves concavity (`Φ_j` and `U` are concave and `U` is increasing). -/
theorem IsConc.plBellOp {V : S.VSpace} (hV : S.IsConc V) : S.IsConc (S.plBellOp V) := by
  intro j
  refine ⟨convex_Icc 0 S.B, fun x hx y hy a b ha hb hab => ?_⟩
  have hxy : a • x + b • y ∈ Icc 0 S.B := convex_Icc 0 S.B hx hy ha hb hab
  have e : ∀ {k : ℝ} (hk : k ∈ Icc 0 S.B), S.vE (S.plBellOp V) j k = S.plBell V j k :=
    fun hk => IccExtend_of_mem _ _ hk
  rw [e hx, e hy, e hxy]
  obtain ⟨zx, hzx, hzxe⟩ := S.exists_plBell_eq V j hx
  obtain ⟨zy, hzy, hzye⟩ := S.exists_plBell_eq V j hy
  rw [← hzxe, ← hzye]
  simp only [smul_eq_mul] at hxy ⊢
  have hPc := (S.Phi_concave j).2 (mem_Ici.2 hx.1) (mem_Ici.2 hy.1) ha hb hab
  simp only [smul_eq_mul] at hPc
  have hzxK : zx ∈ Icc 0 S.B := ⟨hzx.1, hzx.2.trans (S.Phi_le_B j hx)⟩
  have hzyK : zy ∈ Icc 0 S.B := ⟨hzy.1, hzy.2.trans (S.Phi_le_B j hy)⟩
  have hfeas : a * zx + b * zy ∈ Icc 0 (S.Phi j (a * x + b * y)) := by
    refine ⟨by nlinarith [hzx.1, hzy.1], le_trans ?_ hPc⟩
    nlinarith [hzx.2, hzy.2]
  refine le_trans ?_ (S.obj_le_plBell V j hxy hfeas)
  have hcx : 0 ≤ S.Phi j x - zx := by linarith [hzx.2]
  have hcy : 0 ≤ S.Phi j y - zy := by linarith [hzy.2]
  have hU1 := S.U_strictConcave.concaveOn.2 (mem_Ici.2 hcx) (mem_Ici.2 hcy) ha hb hab
  simp only [smul_eq_mul] at hU1
  have hU2 : S.U (a * (S.Phi j x - zx) + b * (S.Phi j y - zy)) ≤
      S.U (S.Phi j (a * x + b * y) - (a * zx + b * zy)) :=
    S.U_strictMono.monotoneOn (mem_Ici.2 (by nlinarith))
      (mem_Ici.2 (by nlinarith)) (by nlinarith)
  have hG : a * ∑ l, S.π j l * S.vE V l zx + b * ∑ l, S.π j l * S.vE V l zy ≤
      ∑ l, S.π j l * S.vE V l (a * zx + b * zy) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun l _ => ?_
    have := (hV l).2 hzxK hzyK ha hb hab
    simp only [smul_eq_mul] at this
    calc a * (S.π j l * S.vE V l zx) + b * (S.π j l * S.vE V l zy)
        = S.π j l * (a * S.vE V l zx + b * S.vE V l zy) := by ring
      _ ≤ S.π j l * S.vE V l (a * zx + b * zy) :=
        mul_le_mul_of_nonneg_left this (S.π_nonneg j l)
  have hβG := mul_le_mul_of_nonneg_left hG S.β_pos'.le
  simp only [obj]
  nlinarith

/-- The iterates `Pⁿ0` are concave. -/
theorem isConc_iterate (n : ℕ) : S.IsConc (S.plBellOp^[n] 0) := by
  induction n with
  | zero => exact S.isConc_zero
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.plBellOp

/-- **The planner's value function is concave** in every state. -/
theorem isConc_Vstar : S.IsConc S.Vstar := by
  intro l
  refine ⟨convex_Icc 0 S.B, fun x hx y hy a b ha hb hab => ?_⟩
  have ht := S.plBellOp_contracting.tendsto_iterate_fixedPoint 0
  have hev : ∀ z, Tendsto (fun n => S.vE (S.plBellOp^[n] 0) l z) atTop
      (𝓝 (S.vE S.Vstar l z)) := fun z =>
    (((continuous_eval_const (projIcc 0 S.B S.B_pos.le z)).comp
      (continuous_apply l)).tendsto _).comp ht
  exact le_of_tendsto_of_tendsto' ((tendsto_const_nhds.smul (hev x)).add
    (tendsto_const_nhds.smul (hev y))) (hev _) fun n => (S.isConc_iterate n l).2 hx hy ha hb hab

/-! ### The planner's policy: positive consumption and the Euler inequality -/

/-- An optimal saving of the planner at `(k, ξ_j)` (`0` outside `K`). -/
noncomputable def pz (j : ι) (k : ℝ) : ℝ :=
  if hk : k ∈ Icc 0 S.B then Classical.choose (S.exists_plBell_eq S.Vstar j hk) else 0

/-- `pz j k` is feasible and optimal. -/
theorem pz_spec (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.pz j k ∈ Icc 0 (S.Phi j k) ∧ S.obj S.Vstar j k (S.pz j k) = S.plBell S.Vstar j k := by
  simp only [pz, hk, ↓reduceDIte]
  exact Classical.choose_spec (S.exists_plBell_eq S.Vstar j hk)

/-- The planner's consumption `Φ_j(k) − pz_j(k)`. -/
noncomputable def pc (j : ι) (k : ℝ) : ℝ := S.Phi j k - S.pz j k

/-- The planner's saving lies in `K`. -/
theorem pz_mem (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) : S.pz j k ∈ Icc 0 S.B :=
  ⟨(S.pz_spec j hk).1.1, (S.pz_spec j hk).1.2.trans (S.Phi_le_B j hk)⟩

/-- **The planner's consumption is positive** (concavity of `V*` and the Inada condition). -/
theorem pc_pos (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) : 0 < S.pc j k := by
  obtain ⟨⟨-, hzP⟩, hzeq⟩ := S.pz_spec j hk
  by_contra hneg
  have hz : S.pz j k = S.Phi j k := by simp only [pc] at hneg; linarith
  have hzpos : 0 < S.Phi j k := S.Phi_pos j hk.1
  have hzK : S.Phi j k ∈ Icc 0 S.B := ⟨hzpos.le, S.Phi_le_B j hk⟩
  set z := S.Phi j k with hzdef
  set M := ‖S.Vstar‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  have key : ∀ δ, 0 < δ → δ < z / 2 → S.U' δ < S.β * (4 * M / z) := by
    intro δ hδ hδz
    have h1 := S.obj_le_plBell S.Vstar j hk (z := z - δ) ⟨by linarith, by linarith⟩
    rw [← hzeq, hz] at h1
    simp only [obj] at h1
    rw [show z - (z - δ) = δ by ring, sub_self] at h1
    have hl : ∀ l, S.vE S.Vstar l z - S.vE S.Vstar l (z - δ) ≤ δ * (4 * M / z) := by
      intro l
      have hs := (S.isConc_Vstar l).slope_anti_adjacent (x := 0) (y := z - δ) (z := z)
        ⟨le_rfl, S.B_pos.le⟩ hzK (by linarith) (by linarith)
      have hb1 := abs_le.1 (S.abs_vE_le S.Vstar l (z - δ))
      have hb2 := abs_le.1 (S.abs_vE_le S.Vstar l 0)
      rw [show z - (z - δ) = δ by ring, sub_zero, div_le_div_iff₀ hδ (by linarith)] at hs
      rw [← mul_div_assoc, le_div_iff₀ hzpos]
      rcases le_or_gt (S.vE S.Vstar l z - S.vE S.Vstar l (z - δ)) 0 with hD | hD
      · nlinarith
      · nlinarith
    have hG : ∑ l, S.π j l * S.vE S.Vstar l z ≤
        ∑ l, S.π j l * S.vE S.Vstar l (z - δ) + δ * (4 * M / z) := by
      have : ∑ l, S.π j l * S.vE S.Vstar l z ≤
          ∑ l, S.π j l * (S.vE S.Vstar l (z - δ) + δ * (4 * M / z)) :=
        Finset.sum_le_sum fun l _ =>
          mul_le_mul_of_nonneg_left (by linarith [hl l]) (S.π_nonneg j l)
      simpa only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, S.π_sum, one_mul]
        using this
    have hsl := S.U_strictConcave.lt_slope_of_hasDerivAt (mem_Ici.2 le_rfl) (mem_Ici.2 hδ.le)
      hδ (S.U_deriv hδ)
    rw [slope_def_field, sub_zero, lt_div_iff₀ hδ] at hsl
    have hβG := mul_le_mul_of_nonneg_left hG S.β_pos'.le
    have : S.U' δ * δ < (S.β * (4 * M / z)) * δ := by nlinarith
    exact lt_of_mul_lt_mul_right this hδ.le
  obtain ⟨δ, hδ1, hδ2⟩ := ((S.isMarginalUtility.inada.eventually_gt_atTop
    (S.β * (4 * M / z))).and (Ioo_mem_nhdsGT (half_pos hzpos))).exists
  exact lt_asymm hδ1 (key δ hδ2.1 hδ2.2)

/-- The one-sided Euler inequality along a perturbation `δ ∈ (0, c)` of the planner's saving. -/
theorem pc_euler_delta (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ < S.pc j k) :
    S.β * (1 - S.θ) * ∑ l, S.π j l * ((S.tech l).f' (S.pz j k + δ) *
      S.U' (S.Phi l (S.pz j k + δ) - S.pz l (S.pz j k))) ≤ S.U' (S.pc j k - δ) := by
  obtain ⟨⟨hz0, hzP⟩, hzeq⟩ := S.pz_spec j hk
  set z := S.pz j k with hzdef
  set c := S.pc j k with hcdef
  have hcz : c = S.Phi j k - z := rfl
  have hzK : z ∈ Icc 0 S.B := S.pz_mem j hk
  have hzδK : z + δ ∈ Icc 0 S.B := ⟨by linarith, by linarith [S.Phi_le_B j hk]⟩
  -- (a) saving `z + δ` is no better than `z`
  have h1 := S.obj_le_plBell S.Vstar j hk (z := z + δ) ⟨by linarith, by linarith⟩
  rw [← hzeq] at h1
  simp only [obj] at h1
  rw [show S.Phi j k - (z + δ) = c - δ by rw [hcz]; ring, ← hcz] at h1
  -- (b) tomorrow's values rise by at least the utility of the extra resources
  have h2 : ∀ l, S.U (S.Phi l (z + δ) - S.pz l z) - S.U (S.Phi l z - S.pz l z) ≤
      S.vE S.Vstar l (z + δ) - S.vE S.Vstar l z := by
    intro l
    obtain ⟨⟨hp0, hpP⟩, hpeq⟩ := S.pz_spec l hzK
    have hb := S.obj_le_plBell S.Vstar l hzδK (z := S.pz l z)
      ⟨hp0, hpP.trans (S.Phi_le l hzK.1 (by linarith))⟩
    rw [← S.vE_Vstar l hzδK] at hb
    rw [S.vE_Vstar l hzK, ← hpeq]
    simp only [obj] at hb ⊢
    linarith
  -- (c) concavity of `U` and the marginal product of `Φ_l`
  have h3 : ∀ l, (1 - S.θ) * δ * (S.tech l).f' (z + δ) *
      S.U' (S.Phi l (z + δ) - S.pz l z) ≤
      S.U (S.Phi l (z + δ) - S.pz l z) - S.U (S.Phi l z - S.pz l z) := by
    intro l
    have ha : 0 < S.Phi l z - S.pz l z := S.pc_pos l hzK
    have hgap := S.Phi_sub_gt l hzK.1 (show z < z + δ by linarith)
    rw [show z + δ - z = δ by ring] at hgap
    have hgap0 : 0 < (1 - S.θ) * δ * (S.tech l).f' (z + δ) :=
      mul_pos (mul_pos (by linarith [S.θ_mem.2]) hδ) ((S.tech l).f'_pos hzδK.1)
    have hb : S.Phi l z - S.pz l z < S.Phi l (z + δ) - S.pz l z := by linarith
    have hsl := S.U_strictConcave.lt_slope_of_hasDerivAt (mem_Ici.2 ha.le)
      (mem_Ici.2 (ha.trans hb).le) hb (S.U_deriv (ha.trans hb))
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at hsl
    have hUp := S.isMarginalUtility.pos _ (ha.trans hb)
    have : (1 - S.θ) * δ * (S.tech l).f' (z + δ) * S.U' (S.Phi l (z + δ) - S.pz l z) ≤
        S.U' (S.Phi l (z + δ) - S.pz l z) * (S.Phi l (z + δ) - S.Phi l z) := by
      rw [mul_comm (S.U' _)]
      exact mul_le_mul_of_nonneg_right hgap.le hUp.le
    have e : S.Phi l (z + δ) - S.pz l z - (S.Phi l z - S.pz l z) =
        S.Phi l (z + δ) - S.Phi l z := by ring
    rw [e] at hsl
    linarith
  -- (d) concavity of `U` today
  have hcδ : 0 < c - δ := by linarith
  have h4 := S.U_strictConcave.slope_lt_of_hasDerivAt (mem_Ici.2 hcδ.le)
    (mem_Ici.2 (by linarith)) (show c - δ < c by linarith) (S.U_deriv hcδ)
  rw [slope_def_field, show c - (c - δ) = δ by ring, div_lt_iff₀ hδ] at h4
  -- combine
  have hsum : ∑ l, S.π j l * ((1 - S.θ) * δ * (S.tech l).f' (z + δ) *
      S.U' (S.Phi l (z + δ) - S.pz l z)) ≤
      ∑ l, S.π j l * S.vE S.Vstar l (z + δ) - ∑ l, S.π j l * S.vE S.Vstar l z := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun l _ => by
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_left ((h3 l).trans (h2 l)) (S.π_nonneg j l)
  have e : ∑ l, S.π j l * ((1 - S.θ) * δ * (S.tech l).f' (z + δ) *
      S.U' (S.Phi l (z + δ) - S.pz l z)) = δ * ((1 - S.θ) * ∑ l, S.π j l *
      ((S.tech l).f' (z + δ) * S.U' (S.Phi l (z + δ) - S.pz l z))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e] at hsum
  have hβ := mul_le_mul_of_nonneg_left hsum S.β_pos'.le
  have : δ * (S.β * (1 - S.θ) * ∑ l, S.π j l * ((S.tech l).f' (z + δ) *
      S.U' (S.Phi l (z + δ) - S.pz l z))) ≤ δ * S.U' (c - δ) := by
    nlinarith
  exact le_of_mul_le_mul_left this hδ

/-- **The planner's Euler inequality** with the agent's after-tax return:
`U′(c_j(k)) ≥ β(1 − θ) Σ_l π_jl f′_l(z) U′(c_l(z))` at the planner's saving `z = pz_j(k)`. -/
theorem pc_euler (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.β * (1 - S.θ) * ∑ l, S.π j l * ((S.tech l).f' (S.pz j k) * S.U' (S.pc l (S.pz j k))) ≤
      S.U' (S.pc j k) := by
  set z := S.pz j k with hzdef
  have hzK : z ∈ Icc 0 S.B := S.pz_mem j hk
  have hc := S.pc_pos j hk
  have hzδ : Tendsto (fun δ : ℝ => z + δ) (𝓝[>] 0) (𝓝[Ici 0] z) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun δ hδ =>
      mem_Ici.2 (by linarith [mem_Ioi.1 hδ, hzK.1])⟩
    exact ((continuous_const.add continuous_id).tendsto' 0 z (add_zero z)).mono_left
      nhdsWithin_le_nhds
  have hL : Tendsto (fun δ : ℝ => S.β * (1 - S.θ) * ∑ l, S.π j l * ((S.tech l).f' (z + δ) *
      S.U' (S.Phi l (z + δ) - S.pz l z))) (𝓝[>] 0)
      (𝓝 (S.β * (1 - S.θ) * ∑ l, S.π j l * ((S.tech l).f' z * S.U' (S.pc l z)))) := by
    refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun l _ => tendsto_const_nhds.mul ?_)
    have hf := ((S.tech l).f'_continuousOn z (mem_Ici.2 hzK.1)).tendsto.comp hzδ
    have hP := (((S.Phi_continuousOn l) z (mem_Ici.2 hzK.1)).tendsto.comp hzδ).sub_const
      (S.pz l z)
    have hU := (S.isMarginalUtility.cont.continuousAt
      (Ioi_mem_nhds (S.pc_pos l hzK))).tendsto.comp hP
    exact hf.mul hU
  have hR : Tendsto (fun δ : ℝ => S.U' (S.pc j k - δ)) (𝓝[>] 0) (𝓝 (S.U' (S.pc j k))) := by
    have h1 : Tendsto (fun δ : ℝ => S.pc j k - δ) (𝓝[>] 0) (𝓝 (S.pc j k)) :=
      ((continuous_const.sub continuous_id).tendsto' 0 (S.pc j k) (by simp)).mono_left
        nhdsWithin_le_nhds
    exact (S.isMarginalUtility.cont.continuousAt (Ioi_mem_nhds hc)).tendsto.comp h1
  refine le_of_tendsto_of_tendsto hL hR ?_
  filter_upwards [Ioo_mem_nhdsGT hc] with δ hδ
  exact S.pc_euler_delta j hk hδ.1 hδ.2

/-! ### The planner's consumption is a floor for the least equilibrium -/

variable {S}

/-- **The floor is invariant under `T`.** If `h ∈ F` leaves at least the planner's consumption,
`ψ_j − h_j ≥ c_j` on `K`, then so does `T h`. At `y₀ = ψ_i(k) − c_i(k) ≥ z = pz_i(k)` every
next-period consumption is at least `c_j(z) > 0`, and the planner's Euler inequality `pc_euler`
puts the right side of (9) below the left side, so `(Th)_i(k) ≤ y₀`. -/
theorem IsInFs.Ts_floor {h : ι → ℝ → ℝ} (hh : S.IsInFs h)
    (hfl : ∀ j, ∀ k ∈ Icc 0 S.B, S.pc j k ≤ (S.tech j).psi k - h j k) (i : ι) {k : ℝ}
    (hk : k ∈ Icc 0 S.B) : S.pc i k ≤ (S.tech i).psi k - S.Ts h i k := by
  have hzK := S.pz_mem i hk
  have hPψ := S.Phi_le_psi i hk.1
  set z := S.pz i k with hzdef
  set y0 := (S.tech i).psi k - S.pc i k with hy0
  have hzy : z ≤ y0 := by simp only [hy0, pc, hzdef]; linarith
  have hy0K : y0 ∈ Icc 0 S.B := ⟨hzK.1.trans hzy, by linarith [S.psi_le_B i hk, S.pc_pos i hk]⟩
  have hcons : ∀ j, S.pc j z ≤ (S.tech j).psi y0 - h j y0 := fun j =>
    (hfl j z hzK).trans (hh.mono_sub j hzK hy0K hzy)
  have hR : S.Rs h i y0 ≤ S.β * (1 - S.θ) * ∑ j, S.π i j * ((S.tech j).f' z *
      S.U' (S.pc j z)) := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) S.coef_pos.le
    have hcj := S.pc_pos j hzK
    refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_
      (S.isMarginalUtility.pos _ (hcj.trans_le (hcons j))).le
      ((S.tech j).f'_pos hzK.1).le) (S.π_nonneg i j)
    · exact (S.tech j).f'_strictAntiOn.antitoneOn (mem_Ici.2 hzK.1) (mem_Ici.2 hy0K.1) hzy
    · exact S.isMarginalUtility.strictAnti.antitoneOn hcj (hcj.trans_le (hcons j)) (hcons j)
  have hnb : ¬ EulerBelow S.U' (S.Zs h i) (S.Rs h i) ((S.tech i).psi k) y0 := by
    intro hb
    rcases hb with ⟨j, -, hj⟩ | hlt
    · linarith [hcons j, S.pc_pos j hzK]
    · rw [show (S.tech i).psi k - y0 = S.pc i k by rw [hy0]; ring] at hlt
      exact absurd (hR.trans (S.pc_euler i hk)) (not_le.2 hlt)
  have := eulerCross_le_of_not_below S.isMarginalUtility (hh.isEulerRHS i) (S.psi_le_B i hk)
    hy0K.1 hnb
  change S.Ts h i k ≤ y0 at this
  linarith

variable (S)

/-- Every iterate `Tⁿ0` leaves at least the planner's consumption. -/
theorem Tsit_floor (n : ℕ) :
    ∀ j, ∀ k ∈ Icc 0 S.B, S.pc j k ≤ (S.tech j).psi k - S.Tsit n j k := by
  induction n with
  | zero =>
    intro j k hk
    have h1 := (S.pz_spec j hk).1.1
    have h2 := S.Phi_le_psi j hk.1
    change S.Phi j k - S.pz j k ≤ (S.tech j).psi k - 0
    linarith
  | succ n ih =>
    intro j k hk
    rw [Tsit_succ]
    exact (S.isInFs_Tsit n).Ts_floor ih j hk

/-- **A consumption floor for the least equilibrium**: consumption under `lfp` is at least the
auxiliary planner's consumption, `ψ_j(k) − lfp_j(k) ≥ c_j(k) > 0`. -/
theorem lfp_floor (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.pc j k ≤ (S.tech j).psi k - S.lfp j k := by
  have : S.lfp j k ≤ (S.tech j).psi k - S.pc j k :=
    le_of_tendsto' (S.tendsto_Tsit j hk) fun n => by linarith [S.Tsit_floor n j k hk]
  linarith

/-- **The least fixed point is non-degenerate**: `lfp_j(k) < ψ_j(k)` for every state and every
`k ∈ K`, for any finite set of technologies. No cross-state condition is needed. -/
theorem lfp_lt_psi (j : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) : S.lfp j k < (S.tech j).psi k := by
  linarith [S.lfp_floor j hk, S.pc_pos j hk]

/-- Under `lfp` no reachable next-period consumption is zero, at any saving `y ∈ K`. -/
theorem lfp_not_Zs (i : ι) {y : ℝ} (hy : y ∈ Icc 0 S.B) : ¬ S.Zs S.lfp i y := by
  rintro ⟨j, -, hj⟩
  linarith [S.lfp_lt_psi j hy]

/-- **The hypothesis of `lfp_equilibrium_of_super` always holds**: `lfp` itself is a
supersolution in `F` with positive consumption on `K`. -/
theorem exists_nondegenerate_super : ∃ hbar : ι → ℝ → ℝ, S.IsInFs hbar ∧
    (∀ j, ∀ k ∈ Icc 0 S.B, S.Ts hbar j k ≤ hbar j k) ∧
    ∀ j, ∀ k ∈ Icc 0 S.B, hbar j k < (S.tech j).psi k :=
  ⟨S.lfp, S.isInFs_lfp, fun j _ hk => (S.Ts_lfp j hk).le, fun j _ hk => S.lfp_lt_psi j hk⟩

/-- **Existence of a non-degenerate stochastic equilibrium, Kuhn–Tucker form** (corrected
p. 560, any finite set of technologies, no cross-state condition). The least fixed point `lfp`
has positive consumption today and in every reachable state tomorrow, and at each `(k, ξ_i)`
either (9) holds as an equation or saving is zero and (9) holds as the inequality
`RHS(0) ≤ U′(ψ_i(k))`. -/
theorem exists_nondegenerate_equilibrium_KT (i : ι) {k : ℝ} (hk : k ∈ Icc 0 S.B) :
    S.lfp i k < (S.tech i).psi k ∧ ¬ S.Zs S.lfp i (S.lfp i k) ∧
      (S.U' ((S.tech i).psi k - S.lfp i k) = S.Rs S.lfp i (S.lfp i k) ∨
        (S.lfp i k = 0 ∧ S.Rs S.lfp i 0 ≤ S.U' ((S.tech i).psi k))) := by
  have hlt := S.lfp_lt_psi i hk
  have hnz := S.lfp_not_Zs i ⟨(S.isInFs_lfp.nonneg i k hk), hlt.le.trans (S.psi_le_B i hk)⟩
  refine ⟨hlt, hnz, ?_⟩
  rcases ex_18_8_spec_KT S.isInFs_lfp i hk with ⟨-, -, h3⟩ | ⟨h1, -⟩ | ⟨h1, -, h3⟩
  · rw [S.Ts_lfp i hk] at h3
    exact Or.inl h3
  · rw [S.Ts_lfp i hk] at h1
    exact absurd h1 hlt.ne
  · rw [S.Ts_lfp i hk] at h1
    exact Or.inr ⟨h1, h3⟩

/-- **Existence of a non-degenerate stochastic equilibrium** (corrected p. 560, any finite set
of technologies). Under the cross-state condition the least fixed point `lfp` solves (9) as an
equation at every `(k, ξ_i)`, with positive consumption today and in every reachable state
tomorrow. This settles the case of different technologies left open by
`exists_nondegenerate_equilibrium_identical`. -/
theorem exists_nondegenerate_equilibrium (hCS : S.CrossState) (i : ι) {k : ℝ}
    (hk : k ∈ Icc 0 S.B) :
    S.lfp i k < (S.tech i).psi k ∧ ¬ S.Zs S.lfp i (S.lfp i k) ∧
      S.U' ((S.tech i).psi k - S.lfp i k) = S.Rs S.lfp i (S.lfp i k) :=
  S.lfp_equilibrium_of_super hCS S.isInFs_lfp (fun j _ hk => (S.Ts_lfp j hk).le)
    (fun j _ hk => S.lfp_lt_psi j hk) i hk

/-- Persistent shocks satisfy the cross-state condition: if `β(1 − θ) π_ii f′_i(0) > 1` for
every state `i`, then `CrossState` holds. -/
theorem crossState_of_persistent
    (h : ∀ i, 1 < S.β * (1 - S.θ) * S.π i i * (S.tech i).f' 0) : S.CrossState := by
  intro i
  have hnn : ∀ j, 0 ≤ S.π i j * ((S.tech j).f' 0 * S.U' ((S.tech j).psi 0)) := fun j =>
    mul_nonneg (S.π_nonneg i j) (mul_nonneg ((S.tech j).f'_pos le_rfl).le
      (S.isMarginalUtility.pos _ ((S.tech j).psi_pos le_rfl)).le)
  have hterm := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  have hU := S.isMarginalUtility.pos _ ((S.tech i).psi_pos le_rfl)
  have h1 := mul_le_mul_of_nonneg_left hterm S.coef_pos.le
  have h2 := h i
  have e : S.β * (1 - S.θ) * (S.π i i * ((S.tech i).f' 0 * S.U' ((S.tech i).psi 0))) =
      (S.β * (1 - S.θ) * S.π i i * (S.tech i).f' 0) * S.U' ((S.tech i).psi 0) := by ring
  nlinarith

end StochModel

/-! ### Examples -/

/-- In `stochJ`, where Exercise 18.8 fails (`ex_18_8_counterexample`), there is still a
non-degenerate equilibrium, in Kuhn–Tucker form. -/
theorem stochJ_nondegenerate (i : Fin 2) {k : ℝ} (hk : k ∈ Icc 0 stochJ.B) :
    stochJ.lfp i k < (stochJ.tech i).psi k :=
  stochJ.lfp_lt_psi i hk

/-- A two-shock model with **different technologies** (`modelHigh` in state `0`, `modelE` in
state `1`) and persistent shocks, `π_ii = 3/4`. -/
noncomputable def stochP : StochModel (Fin 2) where
  tech := ![modelHigh, modelE]
  β := 9 / 10
  θ := 1 / 2
  U := fun c => √c
  U' := fun c => 1 / (2 * √c)
  B := 20
  π := fun i j => if i = j then 3 / 4 else 1 / 4
  tech_β j := by fin_cases j <;> rfl
  tech_θ j := by fin_cases j <;> rfl
  tech_U j := by fin_cases j <;> rfl
  tech_U' j := by fin_cases j <;> rfl
  kbar_le j := by
    fin_cases j
    · exact le_refl (20 : ℝ)
    · change (2 : ℝ) ≤ 20; norm_num
  B_eq := ⟨0, rfl⟩
  π_nonneg _ _ := by split_ifs <;> norm_num
  π_sum i := by fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num

/-- The two technologies of `stochP` differ (`k̄ = 20` against `k̄ = 2`), so
`exists_nondegenerate_equilibrium_identical` does not apply. -/
theorem stochP_tech_ne : stochP.tech 0 ≠ stochP.tech 1 := by
  intro h
  have : (stochP.tech 0).kbar = (stochP.tech 1).kbar := by rw [h]
  change (20 : ℝ) = 2 at this
  norm_num at this

/-- `stochP` satisfies the cross-state condition. -/
theorem stochP_crossState : stochP.CrossState := by
  refine stochP.crossState_of_persistent fun i => ?_
  fin_cases i
  · change 1 < 9 / 10 * (1 - 1 / 2) * (if (0 : Fin 2) = 0 then (3 / 4 : ℝ) else 1 / 4) *
      (441 / 41 / (1 + 0) ^ 2)
    norm_num
  · change 1 < 9 / 10 * (1 - 1 / 2) * (if (1 : Fin 2) = 1 then (3 / 4 : ℝ) else 1 / 4) *
      (891 / 250 / (1 + 0) ^ 2)
    norm_num

/-- **A non-degenerate equilibrium with different technologies**: in `stochP` the least fixed
point solves (9) as an equation everywhere, with positive consumptions. -/
theorem stochP_equilibrium (i : Fin 2) {k : ℝ} (hk : k ∈ Icc 0 stochP.B) :
    stochP.lfp i k < (stochP.tech i).psi k ∧ ¬ stochP.Zs stochP.lfp i (stochP.lfp i k) ∧
      stochP.U' ((stochP.tech i).psi k - stochP.lfp i k) =
        stochP.Rs stochP.lfp i (stochP.lfp i k) :=
  stochP.exists_nondegenerate_equilibrium stochP_crossState i hk

end StokeyLucasPrescott.EquilibriaWithDistortions
