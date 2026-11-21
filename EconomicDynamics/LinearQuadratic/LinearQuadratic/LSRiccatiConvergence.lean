/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LinearQuadratic.LSStateSpace

/-!
# Convergence of the Riccati iteration (the undiscounted core of Propositions 9.3.1–9.3.2)

Miao, §9.3, pp. 298–301, for an undiscounted LQ problem `(Q, R, A, B)` in the
Sargent–Stachurski form `SS.LQProblem` (Riccati map `R(P)`, gain `F(P) = −G(P)⁻¹B'PA`, closed
loop `A + BF`). The discounted problem of the book is the case `(√βA, √βB)`
(`LSInfiniteHorizon`). This module proves the existence of the Riccati fixed point that
`SS.LQProblem.optimality` takes as a hypothesis.

* `ls_riccati_mono`: the Riccati map is monotone in the Loewner order (it is the minimum of the
  monotone maps `T_F`); `ls_iter_zero_mono`: `R^s(0)` increases in `s`.
* `ls_finite_lower`: every control sequence costs at least `x₀'R^s(P₀)x₀` over `s` periods with
  terminal cost `P₀` (the finite-horizon optimality of the Riccati iterates).
* `ls_iter_le_PF` (stabilizable case: the cost of a stable feedback bounds `R^s(0)`) and
  `ls_iter_bdd_of_controllable` (controllable case: steer to zero in `nₓ` steps).
* `ls_iter_converges`: bounded monotone iterates converge to a positive semidefinite limit;
  `ls_tendsto_riccati`: `R` is continuous on the positive semidefinite cone; the limit is a fixed
  point.
* `ls_stable_of_fixed`: along the closed loop `x'Px − x₊'Px₊ = x'(Q + F'RF)x`, so the costs are
  summable and tend to zero (9.14); under a detection condition `ls_Detects` this forces
  `xₜ → 0`, i.e. `A + BF(P)` is stable. The detection condition holds if `Q > 0`
  (`ls_detects_of_posDef`), if `Q = L'L` with `(A, L)` detectable (`ls_detects_of_detectable`)
  or observable (`ls_detects_of_observable`).
* `ls_riccati_main`: existence and uniqueness of the positive semidefinite fixed point,
  convergence `R^s(P₀) → P` from every positive semidefinite `P₀`, stability of `F(P)`, and
  `P = P_{F(P)}`.
-/

open Filter Topology Matrix

open scoped MatrixOrder

namespace Miao.LinearQuadratic

variable {K U : Type*} [Fintype K] [DecidableEq K] [Fintype U] [DecidableEq U]
  (L : SS.LQProblem K U)

omit [DecidableEq K] in
/-- `R(P) ≤ T_F(P)` for every `F`. -/
theorem ls_riccati_le_TF {P : Matrix K K ℝ} (hP : P.PosSemidef) (F : Matrix U K ℝ) :
    L.riccati P ≤ L.TF F P := by
  rw [L.riccati_eq_TF hP]
  exact (L.gain_iff_TF_le hP _).1 rfl F

omit [Fintype K] [DecidableEq K] in
theorem ls_posSemidef_of_le {P P' : Matrix K K ℝ} (hP : P.PosSemidef) (h : P ≤ P') :
    P'.PosSemidef := by
  have := hP.add (Matrix.le_iff.1 h)
  rwa [add_sub_cancel] at this

omit [DecidableEq K] in
/-- `P ≤ P'` gives `v'Pv ≤ v'P'v`. -/
theorem ls_quad_le {P P' : Matrix K K ℝ} (h : P ≤ P') (v : K → ℝ) :
    v ⬝ᵥ (P *ᵥ v) ≤ v ⬝ᵥ (P' *ᵥ v) := by
  have := (SS.LQProblem.posSemidef_iff_real.1 (Matrix.le_iff.1 h)).2 v
  rw [sub_mulVec, dotProduct_sub, sub_nonneg] at this
  exact this

omit [DecidableEq K] in
/-- The Riccati map is monotone in the Loewner order. -/
theorem ls_riccati_mono {P P' : Matrix K K ℝ} (hP : P.PosSemidef) (h : P ≤ P') :
    L.riccati P ≤ L.riccati P' := by
  have hP' := ls_posSemidef_of_le hP h
  calc L.riccati P ≤ L.TF (L.gain P') P := ls_riccati_le_TF L hP _
    _ ≤ L.TF (L.gain P') P' := L.TF_mono _ h
    _ = L.riccati P' := (L.riccati_eq_TF hP').symm

omit [DecidableEq K] in
theorem ls_iter_psd {P : Matrix K K ℝ} (hP : P.PosSemidef) (s : ℕ) :
    (L.riccati^[s] P).PosSemidef := by
  induction s with
  | zero => exact hP
  | succ s ih => rw [Function.iterate_succ_apply']; exact L.riccati_posSemidef ih

omit [DecidableEq K] in
theorem ls_iter_mono_le {P P' : Matrix K K ℝ} (hP : P.PosSemidef) (h : P ≤ P') (s : ℕ) :
    L.riccati^[s] P ≤ L.riccati^[s] P' := by
  induction s with
  | zero => exact h
  | succ s ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact ls_riccati_mono L (ls_iter_psd L hP s) ih

omit [Fintype K] [DecidableEq K] in
theorem ls_zero_le_psd {P : Matrix K K ℝ} (hP : P.PosSemidef) : 0 ≤ P := by
  rw [Matrix.le_iff, sub_zero]
  exact hP

omit [DecidableEq K] in
/-- `R^s(0) ≤ R^{s+1}(0)`: the Riccati iterates from `0` increase. -/
theorem ls_iter_zero_mono (s : ℕ) : L.riccati^[s] 0 ≤ L.riccati^[s + 1] 0 := by
  rw [Function.iterate_succ_apply]
  exact ls_iter_mono_le L PosSemidef.zero (ls_zero_le_psd (L.riccati_posSemidef PosSemidef.zero)) s

omit [DecidableEq K] in
theorem ls_iter_zero_mono_add (s m : ℕ) : L.riccati^[s] 0 ≤ L.riccati^[s + m] 0 := by
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact ih.trans (ls_iter_zero_mono L (s + m))

omit [DecidableEq K] in
/-- Finite-horizon optimality of the Riccati iterates: for every control sequence with
`x_{t+1} = Ax_t + Bu_t`, `x₀'R^s(P₀)x₀ ≤ ∑_{t<s}(x_t'Qx_t + u_t'Ru_t) + x_s'P₀x_s`. -/
theorem ls_finite_lower {P₀ : Matrix K K ℝ} (hP₀ : P₀.PosSemidef) (s : ℕ) :
    ∀ (x : ℕ → K → ℝ) (u : ℕ → U → ℝ), (∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ u t) →
      x 0 ⬝ᵥ (L.riccati^[s] P₀ *ᵥ x 0) ≤
        ∑ t ∈ Finset.range s, (x t ⬝ᵥ (L.Q *ᵥ x t) + u t ⬝ᵥ (L.R *ᵥ u t)) +
          x s ⬝ᵥ (P₀ *ᵥ x s) := by
  induction s with
  | zero => intro x u _; simp
  | succ s ih =>
    intro x u hx
    have hP := ls_iter_psd L hP₀ s
    have h1 : x 0 ⬝ᵥ (L.riccati^[s + 1] P₀ *ᵥ x 0) ≤ L.cost (L.riccati^[s] P₀) (x 0) (u 0) := by
      rw [Function.iterate_succ_apply', L.riccati_eq_TF hP, L.dotProduct_TF]
      exact (L.gain_isMinimizer hP (x 0)).1 _
    have h2 := ih (fun t => x (t + 1)) (fun t => u (t + 1)) fun t => hx (t + 1)
    have h3 : L.cost (L.riccati^[s] P₀) (x 0) (u 0) = x 0 ⬝ᵥ (L.Q *ᵥ x 0) +
        u 0 ⬝ᵥ (L.R *ᵥ u 0) + x 1 ⬝ᵥ (L.riccati^[s] P₀ *ᵥ x 1) := by
      rw [SS.LQProblem.cost, hx 0]
    rw [Finset.sum_range_succ']
    linarith

/-- The stabilizable case (Miao, p. 299): a stable feedback `F` bounds the iterates,
`R^s(0) ≤ P_F`. -/
theorem ls_iter_le_PF [Nonempty K] {F : Matrix U K ℝ} (hF : L.IsStable F) (s : ℕ) :
    L.riccati^[s] 0 ≤ L.PF F := by
  induction s with
  | zero => exact ls_zero_le_psd hF.PF_posSemidef
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    calc L.riccati (L.riccati^[s] 0) ≤ L.TF F (L.riccati^[s] 0) :=
          ls_riccati_le_TF L (ls_iter_psd L PosSemidef.zero s) F
      _ ≤ L.TF F (L.PF F) := L.TF_mono F ih
      _ = L.PF F := hF.TF_PF

/-- The controllable case (Miao, p. 299): steering `x₀` to zero in `nₓ` steps and holding it
there bounds `x₀'R^s(0)x₀` uniformly in `s`. -/
theorem ls_iter_bdd_of_controllable (hc : ls_Controllable L.A L.B) (x₀ : K → ℝ) :
    ∃ c, ∀ s, x₀ ⬝ᵥ (L.riccati^[s] 0 *ᵥ x₀) ≤ c := by
  obtain ⟨u, hu0, hun⟩ := ls_reach_of_gram hc x₀ 0
  set n := Fintype.card K
  set x := ls_traj L.A L.B x₀ u
  have hx : ∀ t, x (t + 1) = L.A *ᵥ x t + L.B *ᵥ u t := fun t => rfl
  have hxz : ∀ m, x (n + m) = 0 := by
    intro m
    induction m with
    | zero => exact hun
    | succ m ih => rw [← add_assoc, hx, ih, hu0 _ (by omega)]; simp
  refine ⟨∑ t ∈ Finset.range n, (x t ⬝ᵥ (L.Q *ᵥ x t) + u t ⬝ᵥ (L.R *ᵥ u t)), fun s => ?_⟩
  have h1 := ls_quad_le (ls_iter_zero_mono_add L s n) x₀
  have h2 := ls_finite_lower L PosSemidef.zero (s + n) x u hx
  rw [show s + n = n + s by ring, Finset.sum_range_add, hxz s] at h2
  have hz : ∑ t ∈ Finset.range s, (x (n + t) ⬝ᵥ (L.Q *ᵥ x (n + t)) +
      u (n + t) ⬝ᵥ (L.R *ᵥ u (n + t))) = 0 :=
    Finset.sum_eq_zero fun t _ => by rw [hxz t, hu0 _ (by omega)]; simp
  rw [hz] at h2
  have h0 : x 0 = x₀ := rfl
  rw [h0, show n + s = s + n by ring] at h2
  simp only [add_zero, zero_mulVec, dotProduct_zero] at h2
  exact h1.trans h2

omit [DecidableEq K] in
/-- Quadratic forms are continuous in the matrix. -/
theorem ls_tendsto_quad {M : ℕ → Matrix K K ℝ} {M₀ : Matrix K K ℝ}
    (h : Tendsto M atTop (𝓝 M₀)) (v : K → ℝ) :
    Tendsto (fun s => v ⬝ᵥ (M s *ᵥ v)) atTop (𝓝 (v ⬝ᵥ (M₀ *ᵥ v))) :=
  ((Continuous.dotProduct continuous_const
    (Continuous.matrix_mulVec continuous_id continuous_const)).tendsto M₀).comp h

omit [DecidableEq K] in
/-- Bounded Riccati iterates from `0` converge to a positive semidefinite limit. -/
theorem ls_iter_converges (hbdd : ∀ x₀ : K → ℝ, ∃ c, ∀ s, x₀ ⬝ᵥ (L.riccati^[s] 0 *ᵥ x₀) ≤ c) :
    ∃ P : Matrix K K ℝ, P.PosSemidef ∧ Tendsto (fun s => L.riccati^[s] 0) atTop (𝓝 P) := by
  have hsym : ∀ s, (L.riccati^[s] 0)ᵀ = L.riccati^[s] 0 := fun s =>
    (SS.LQProblem.posSemidef_iff_real.1 (ls_iter_psd L PosSemidef.zero s)).1
  have hq : ∀ v : K → ℝ, ∃ c, Tendsto (fun s => v ⬝ᵥ (L.riccati^[s] 0 *ᵥ v)) atTop (𝓝 c) := by
    intro v
    obtain ⟨c, hc⟩ := hbdd v
    have hmono : Monotone fun s => v ⬝ᵥ (L.riccati^[s] 0 *ᵥ v) :=
      monotone_nat_of_le_succ fun s => ls_quad_le (ls_iter_zero_mono L s) v
    exact ⟨_, tendsto_atTop_ciSup hmono ⟨c, by rintro _ ⟨s, rfl⟩; exact hc s⟩⟩
  obtain ⟨P, -, hP⟩ := ls_exists_tendsto_of_quad hsym hq
  exact ⟨P, posSemidef_is_closed.mem_of_tendsto hP
    (Eventually.of_forall fun s => ls_iter_psd L PosSemidef.zero s), hP⟩

omit [DecidableEq K] in
/-- Products of convergent matrix sequences converge. -/
theorem ls_tendsto_mul {m n p : Type*} [Fintype n] {f : ℕ → Matrix m n ℝ} {g : ℕ → Matrix n p ℝ}
    {a : Matrix m n ℝ} {b : Matrix n p ℝ} (hf : Tendsto f atTop (𝓝 a))
    (hg : Tendsto g atTop (𝓝 b)) : Tendsto (fun s => f s * g s) atTop (𝓝 (a * b)) :=
  ((Continuous.matrix_mul continuous_fst continuous_snd).tendsto (a, b)).comp (hf.prodMk_nhds hg)

omit [DecidableEq K] in
/-- Inversion is continuous at an invertible matrix. -/
theorem ls_tendsto_inv {f : ℕ → Matrix U U ℝ} {a : Matrix U U ℝ} (ha : IsUnit a.det)
    (hf : Tendsto f atTop (𝓝 a)) : Tendsto (fun s => (f s)⁻¹) atTop (𝓝 a⁻¹) := by
  have h : ContinuousAt Ring.inverse a.det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ ha.ne_zero
  exact (continuousAt_matrix_inv a h).tendsto.comp hf

omit [DecidableEq K] in
/-- The gain `F(P)` is continuous on the positive semidefinite cone. -/
theorem ls_tendsto_gain {Pn : ℕ → Matrix K K ℝ} {P : Matrix K K ℝ} (hP : P.PosSemidef)
    (h : Tendsto Pn atTop (𝓝 P)) : Tendsto (fun n => L.gain (Pn n)) atTop (𝓝 (L.gain P)) := by
  have hG : Tendsto (fun n => L.gainDen (Pn n)) atTop (𝓝 (L.gainDen P)) :=
    (ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds).add
      tendsto_const_nhds
  have hGi := ls_tendsto_inv ((isUnit_iff_isUnit_det _).1 (L.gainDen_posDef hP).isUnit) hG
  exact (ls_tendsto_mul (ls_tendsto_mul (ls_tendsto_mul hGi tendsto_const_nhds) h)
    tendsto_const_nhds).neg

omit [DecidableEq K] in
/-- The Riccati map is continuous on the positive semidefinite cone. -/
theorem ls_tendsto_riccati {Pn : ℕ → Matrix K K ℝ} {P : Matrix K K ℝ} (hP : P.PosSemidef)
    (h : Tendsto Pn atTop (𝓝 P)) :
    Tendsto (fun n => L.riccati (Pn n)) atTop (𝓝 (L.riccati P)) := by
  have hG : Tendsto (fun n => L.gainDen (Pn n)) atTop (𝓝 (L.gainDen P)) :=
    (ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds).add
      tendsto_const_nhds
  have hGi := ls_tendsto_inv ((isUnit_iff_isUnit_det _).1 (L.gainDen_posDef hP).isUnit) hG
  have hAPA : Tendsto (fun n => L.Aᵀ * Pn n * L.A) atTop (𝓝 (L.Aᵀ * P * L.A)) :=
    ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds
  have hmid : Tendsto (fun n => L.Aᵀ * Pn n * L.B * (L.gainDen (Pn n))⁻¹ * L.Bᵀ * Pn n * L.A)
      atTop (𝓝 (L.Aᵀ * P * L.B * (L.gainDen P)⁻¹ * L.Bᵀ * P * L.A)) :=
    ls_tendsto_mul (ls_tendsto_mul (ls_tendsto_mul (ls_tendsto_mul
      (ls_tendsto_mul (ls_tendsto_mul tendsto_const_nhds h) tendsto_const_nhds) hGi)
      tendsto_const_nhds) h) tendsto_const_nhds
  exact (hAPA.sub hmid).add tendsto_const_nhds

omit [DecidableEq K] in
/-- A positive semidefinite limit of the iterates `R^s(P₀)` is a fixed point of `R`. -/
theorem ls_fixed_of_tendsto {P₀ P : Matrix K K ℝ} (hP : P.PosSemidef)
    (h : Tendsto (fun s => L.riccati^[s] P₀) atTop (𝓝 P)) : L.riccati P = P := by
  have h1 := ls_tendsto_riccati L hP h
  have h2 : Tendsto (fun s => L.riccati^[s + 1] P₀) atTop (𝓝 P) :=
    (tendsto_add_atTop_iff_nat 1).2 h
  simp only [Function.iterate_succ_apply'] at h2
  exact tendsto_nhds_unique h1 h2

/-- The detection condition: along the closed loop `x_{t+1} = (A + BF)x_t`, `x_t'Qx_t → 0` and
`Fx_t → 0` force `x_t → 0`. -/
def ls_Detects (F : Matrix U K ℝ) : Prop :=
  ∀ x : ℕ → K → ℝ, (∀ t, x (t + 1) = L.closedLoop F *ᵥ x t) →
    Tendsto (fun t => x t ⬝ᵥ (L.Q *ᵥ x t)) atTop (𝓝 0) →
    Tendsto (fun t => F *ᵥ x t) atTop (𝓝 0) → Tendsto x atTop (𝓝 0)

omit [DecidableEq K] in
/-- (9.14) (Miao, p. 300): at a fixed point `P = R(P)`, along the closed loop
`x_{t+1} = (A + BF(P))x_t` the costs `x_t'(Q + F'RF)x_t` are summable (with sum at most
`x₀'Px₀`), hence `x_t'Qx_t → 0` and `F(P)x_t → 0`. -/
theorem ls_cost_tendsto_zero {P : Matrix K K ℝ} (hP : P.PosSemidef) (hfix : L.riccati P = P)
    {x : ℕ → K → ℝ} (hx : ∀ t, x (t + 1) = L.closedLoop (L.gain P) *ᵥ x t) :
    (∀ n, ∑ t ∈ Finset.range n, x t ⬝ᵥ (L.costMat (L.gain P) *ᵥ x t) =
      x 0 ⬝ᵥ (P *ᵥ x 0) - x n ⬝ᵥ (P *ᵥ x n)) ∧
    Tendsto (fun t => x t ⬝ᵥ (L.Q *ᵥ x t)) atTop (𝓝 0) ∧
    Tendsto (fun t => L.gain P *ᵥ x t) atTop (𝓝 0) := by
  set F := L.gain P
  have hTF : P = L.costMat F + (L.closedLoop F)ᵀ * P * L.closedLoop F := by
    conv_lhs => rw [← hfix, L.riccati_eq_TF hP, SS.LQProblem.TF_eq]
  have hstep : ∀ t, x t ⬝ᵥ (P *ᵥ x t) =
      x t ⬝ᵥ (L.costMat F *ᵥ x t) + x (t + 1) ⬝ᵥ (P *ᵥ x (t + 1)) := by
    intro t
    conv_lhs => rw [hTF]
    rw [add_mulVec, dotProduct_add, SS.LQProblem.dotProduct_transpose_mul_mul, ← hx t]
  have hsum : ∀ n, ∑ t ∈ Finset.range n, x t ⬝ᵥ (L.costMat F *ᵥ x t) =
      x 0 ⬝ᵥ (P *ᵥ x 0) - x n ⬝ᵥ (P *ᵥ x n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, hstep n]; ring
  have hPq := (SS.LQProblem.posSemidef_iff_real.1 hP).2
  have hRq := (SS.LQProblem.posSemidef_iff_real.1 L.R_pd.posSemidef).2
  have hQq := (SS.LQProblem.posSemidef_iff_real.1 L.Q_psd).2
  have hsplit : ∀ t, x t ⬝ᵥ (L.costMat F *ᵥ x t) =
      (F *ᵥ x t) ⬝ᵥ (L.R *ᵥ (F *ᵥ x t)) + x t ⬝ᵥ (L.Q *ᵥ x t) := by
    intro t
    rw [SS.LQProblem.costMat, add_mulVec, dotProduct_add,
      SS.LQProblem.dotProduct_transpose_mul_mul]
  have hnn : ∀ t, 0 ≤ x t ⬝ᵥ (L.costMat F *ᵥ x t) := fun t => by
    rw [hsplit]; exact add_nonneg (hRq _) (hQq _)
  have hs : Summable fun t => x t ⬝ᵥ (L.costMat F *ᵥ x t) :=
    summable_of_sum_range_le hnn fun n => by rw [hsum n]; linarith [hPq (x n)]
  have h0 := hs.tendsto_atTop_zero
  refine ⟨hsum, ?_, ?_⟩
  · refine squeeze_zero (fun t => hQq _) (fun t => ?_) h0
    rw [hsplit]
    linarith [hRq (F *ᵥ x t)]
  · refine ls_tendsto_zero_of_quad_posDef L.R_pd ?_
    refine squeeze_zero (fun t => hRq _) (fun t => ?_) h0
    rw [hsplit]
    linarith [hQq (x t)]

omit [DecidableEq K] in
/-- Miao, p. 300: under the detection condition, the closed loop of a fixed point is stable. -/
theorem ls_stable_of_fixed [Nonempty K] {P : Matrix K K ℝ} (hP : P.PosSemidef)
    (hfix : L.riccati P = P) (hD : ls_Detects L (L.gain P)) : L.IsStable (L.gain P) := by
  classical
  rw [SS.LQProblem.IsStable, ← ls_stable_iff_specRad, ls_stable_iff_tendsto]
  intro v
  have hx : ∀ t, (L.closedLoop (L.gain P) ^ (t + 1)) *ᵥ v =
      L.closedLoop (L.gain P) *ᵥ ((L.closedLoop (L.gain P) ^ t) *ᵥ v) := fun t => by
    rw [pow_succ', mulVec_mulVec]
  obtain ⟨-, hQ, hF⟩ := ls_cost_tendsto_zero L hP hfix
    (x := fun t => (L.closedLoop (L.gain P) ^ t) *ᵥ v) hx
  exact hD _ hx hQ hF

omit [DecidableEq K] [DecidableEq U] in
/-- The detection condition when `Q > 0` (Proposition 9.3.1). -/
theorem ls_detects_of_posDef (hQ : L.Q.PosDef) (F : Matrix U K ℝ) : ls_Detects L F :=
  fun _ _ hq _ => ls_tendsto_zero_of_quad_posDef hQ hq

omit [DecidableEq K] in
theorem ls_tendsto_mulVec_zero {m n : Type*} [Fintype n] (M : Matrix m n ℝ) {z : ℕ → n → ℝ}
    (hz : Tendsto z atTop (𝓝 0)) : Tendsto (fun t => M *ᵥ z t) atTop (𝓝 0) := by
  have := ((Continuous.matrix_mulVec (continuous_const (y := M)) continuous_id).tendsto
    (0 : n → ℝ)).comp hz
  simpa [Function.comp_def] using this

omit [DecidableEq K] [DecidableEq U] in
/-- With `Q = L'L`, `x_t'Qx_t → 0` gives `Lx_t → 0`. -/
theorem ls_tendsto_L {Y : Type*} [Fintype Y] {Lm : Matrix Y K ℝ} (hQ : L.Q = Lmᵀ * Lm)
    {x : ℕ → K → ℝ} (hq : Tendsto (fun t => x t ⬝ᵥ (L.Q *ᵥ x t)) atTop (𝓝 0)) :
    Tendsto (fun t => Lm *ᵥ x t) atTop (𝓝 0) := by
  classical
  refine ls_tendsto_zero_of_quad_posDef PosDef.one ?_
  refine hq.congr fun t => ?_
  rw [hQ, one_mulVec, ← mulVec_mulVec, ← SS.LQProblem.mulVec_dotProduct]

omit [DecidableEq U] in
/-- The detection condition when `Q = L'L` with `(A, L)` detectable (Proposition 9.3.2): with
`A − HL` stable, `x_{t+1} = (A − HL)x_t + HLx_t + BFx_t` is a stable system with vanishing
input. -/
theorem ls_detects_of_detectable {Y : Type*} [Fintype Y] {Lm : Matrix Y K ℝ}
    (hQ : L.Q = Lmᵀ * Lm) (hd : ls_Detectable L.A Lm) (F : Matrix U K ℝ) : ls_Detects L F := by
  obtain ⟨H, hH⟩ := hd
  intro x hx hq hF
  have hL := ls_tendsto_L L hQ hq
  refine ls_tendsto_zero_of_stable_input hH (w := fun t => H *ᵥ (Lm *ᵥ x t) + L.B *ᵥ (F *ᵥ x t))
    (fun t => ?_) ?_
  · rw [hx, SS.LQProblem.closedLoop, sub_mulVec, add_mulVec, mulVec_mulVec, mulVec_mulVec]
    abel
  · simpa using (ls_tendsto_mulVec_zero H hL).add (ls_tendsto_mulVec_zero L.B hF)

omit [DecidableEq U] in
/-- The detection condition when `Q = L'L` with `(A, L)` observable (Proposition 9.3.2): for each
`j`, `x_{t+j} − Aʲx_t → 0`, hence `LAʲx_t → 0` and `Wx_t → 0` for the positive definite
observability Gramian `W`. -/
theorem ls_detects_of_observable {Y : Type*} [Fintype Y] {Lm : Matrix Y K ℝ}
    (hQ : L.Q = Lmᵀ * Lm) (ho : ls_Observable L.A Lm) (F : Matrix U K ℝ) : ls_Detects L F := by
  intro x hx hq hF
  have hL := ls_tendsto_L L hQ hq
  have hshift : ∀ j, Tendsto (fun t => x (t + j) - (L.A ^ j) *ᵥ x t) atTop (𝓝 0) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : ∀ t, x (t + (j + 1)) - (L.A ^ (j + 1)) *ᵥ x t =
          L.A *ᵥ (x (t + j) - (L.A ^ j) *ᵥ x t) + L.B *ᵥ (F *ᵥ x (t + j)) := by
        intro t
        rw [← add_assoc, hx, SS.LQProblem.closedLoop, add_mulVec, pow_succ', ← mulVec_mulVec,
          mulVec_sub, ← mulVec_mulVec]
        abel
      have hFj : Tendsto (fun t => F *ᵥ x (t + j)) atTop (𝓝 0) :=
        hF.comp (tendsto_add_atTop_nat j)
      simpa [e] using (ls_tendsto_mulVec_zero L.A ih).add (ls_tendsto_mulVec_zero L.B hFj)
  have hLj : ∀ j, Tendsto (fun t => (Lm * L.A ^ j) *ᵥ x t) atTop (𝓝 0) := by
    intro j
    have h1 : Tendsto (fun t => Lm *ᵥ x (t + j)) atTop (𝓝 0) := hL.comp (tendsto_add_atTop_nat j)
    have h2 := ls_tendsto_mulVec_zero Lm (hshift j)
    have := h1.sub h2
    simp only [sub_zero] at this
    refine this.congr fun t => ?_
    rw [mulVec_sub, ← mulVec_mulVec]
    abel
  set W := ls_gram L.Aᵀ Lmᵀ (Fintype.card K)
  have hW : Tendsto (fun t => W *ᵥ x t) atTop (𝓝 0) := by
    have e : ∀ t, W *ᵥ x t = ∑ j ∈ Finset.range (Fintype.card K),
        (L.Aᵀ ^ j * Lmᵀ) *ᵥ ((Lm * L.A ^ j) *ᵥ x t) := by
      intro t
      simp only [W, ls_gram, Matrix.sum_mulVec, transpose_transpose, mulVec_mulVec,
        Matrix.mul_assoc]
    have := tendsto_finsetSum (Finset.range (Fintype.card K))
      fun j _ => ls_tendsto_mulVec_zero (L.Aᵀ ^ j * Lmᵀ) (hLj j)
    simp only [Finset.sum_const_zero] at this
    exact this.congr fun t => (e t).symm
  have hu : IsUnit W.det := (isUnit_iff_isUnit_det _).1 ho.isUnit
  have := ls_tendsto_mulVec_zero W⁻¹ hW
  refine this.congr fun t => ?_
  rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]

/-- The Riccati iterates converge to the positive semidefinite fixed point (Propositions
9.3.1–9.3.2, undiscounted form). Suppose `(A, B)` is stabilizable (some stable `F`) or
controllable, and the detection condition holds for every feedback. Then the Riccati equation
`P = R(P)` has a positive semidefinite solution `P`, unique among positive semidefinite matrices;
`R^s(P₀) → P` from every positive semidefinite `P₀`; `F(P)` is stable; and `P = P_{F(P)}`. -/
theorem ls_riccati_main [Nonempty K] (hstab : (∃ F, L.IsStable F) ∨ ls_Controllable L.A L.B)
    (hD : ∀ F, ls_Detects L F) :
    ∃ P : Matrix K K ℝ, P.PosSemidef ∧ L.riccati P = P ∧ L.IsStable (L.gain P) ∧
      P = L.PF (L.gain P) ∧
      (∀ P₀ : Matrix K K ℝ, P₀.PosSemidef → Tendsto (fun s => L.riccati^[s] P₀) atTop (𝓝 P)) ∧
      ∀ P' : Matrix K K ℝ, P'.PosSemidef → L.riccati P' = P' → P' = P := by
  have hbdd : ∀ x₀ : K → ℝ, ∃ c, ∀ s, x₀ ⬝ᵥ (L.riccati^[s] 0 *ᵥ x₀) ≤ c := by
    rcases hstab with ⟨F, hF⟩ | hc
    · exact fun x₀ => ⟨_, fun s => ls_quad_le (ls_iter_le_PF L hF s) x₀⟩
    · exact ls_iter_bdd_of_controllable L hc
  obtain ⟨P, hP, hlim⟩ := ls_iter_converges L hbdd
  have hfix := ls_fixed_of_tendsto L hP hlim
  have hst := ls_stable_of_fixed L hP hfix (hD _)
  have hTF : L.TF (L.gain P) P = P := by rw [← L.riccati_eq_TF hP, hfix]
  have hPF : P = L.PF (L.gain P) := hst.eq_PF hTF
  have hconv : ∀ P₀ : Matrix K K ℝ, P₀.PosSemidef →
      Tendsto (fun s => L.riccati^[s] P₀) atTop (𝓝 P) := by
    intro P₀ hP₀
    set F := L.gain P
    have hup : ∀ s, L.riccati^[s] P₀ ≤ (L.TF F)^[s] P₀ := by
      intro s
      induction s with
      | zero => exact le_rfl
      | succ s ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact (ls_riccati_le_TF L (ls_iter_psd L hP₀ s) F).trans (L.TF_mono F ih)
    have hlow : ∀ s, L.riccati^[s] 0 ≤ L.riccati^[s] P₀ := fun s =>
      ls_iter_mono_le L PosSemidef.zero (ls_zero_le_psd hP₀) s
    have hTlim : Tendsto (fun s => (L.TF F)^[s] P₀) atTop (𝓝 P) := by
      rw [hPF]
      exact tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => hst.tendsto_TF_iterate P₀ a b
    refine ls_tendsto_of_quad (fun s => (SS.LQProblem.posSemidef_iff_real.1
      (ls_iter_psd L hP₀ s)).1) (SS.LQProblem.posSemidef_iff_real.1 hP).1 fun v => ?_
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (ls_tendsto_quad hlim v)
      (ls_tendsto_quad hTlim v) (fun s => ls_quad_le (hlow s) v) (fun s => ls_quad_le (hup s) v)
  refine ⟨P, hP, hfix, hst, hPF, hconv, fun P' hP' hfix' => ?_⟩
  have h := hconv P' hP'
  have hc : (fun s => L.riccati^[s] P') = fun _ => P' :=
    funext fun s => Function.iterate_fixed hfix' s
  rw [hc] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

end Miao.LinearQuadratic
