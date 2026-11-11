/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.KFExamples

/-!
# Exercises 10.1–10.5

Miao, §10.4, p. 345 (items 1–5). All filters are in the linear-projection (second-moment) reading
of `KFFilter`.

* **Exercise 10.1**: `y_t = μ + ε_t + bε_{t−1}` in the form (10.3)–(10.4) with
  `x_t = (ε_t, ε_{t−1})'`
  and `z_t = 1` (`ex_10_1`).
* **Exercise 10.2**: with `ρ` unknown, the state `(ρ, z_t)` has the non-linear transition
  `(ρ, z) ↦ (ρ, ρz)`, which no matrix represents (`ex_10_2_nonlinear`): the Kalman filter does not
  apply to `(ρ, z_t)`. What is proved is the Kalman filter conditional on `ρ` (`ex_10_2`): the
  scalar filter with `a = ρ`, `c = σ_η`, `d = σ_v`, its gain and Riccati recursion, and its
  convergence. (A filter for the unknown `ρ` would be a non-linear filter, §10.1.2.)
* **Exercise 10.3**: `x_t = θ`, `y_t = θ + v_t`, `θ ∼ (μ, Σ₀)`: `Σ_{t|t−1} = Σ₀R/(R + tΣ₀)`,
  `K_t = Σ₀/(R + (t + 1)Σ₀)`, `x̂_{t|t−1} = (Rμ + Σ₀∑_{s<t}y_s)/(R + tΣ₀)` (`ex_10_3`); in the
  long run `Σ_{t|t−1} → 0` and `K_t → 0`, and the mean squared error of `x̂_{t|t}` tends to `0`
  (`ex_10_3_mse`).
* **Exercise 10.4**: the timing `x_{t+1} = Ax_t + Bu_t + Cε_{t+1}`, `y_{t+1} = Gx_t + Hu_t +
  Dε_{t+1}`. The filter `x̂_{t+1} = Ax̂_t + Bu_t + K_t(y_{t+1} − Gx̂_t − Hu_t)` with
  `K_t = (AΣ_tG' + CD')(GΣ_tG' + DD')⁻¹` and `Σ_{t+1} = T̂(Σ_t)`, `T̂` the Riccati operator (9.11)
  of
  the dual LQ problem `(A', G', CC', DD', CD', β = 1)` (`kf_ex4Dual`): the error recursion, the
  second moments `Σ_t`, and the optimality of `K_t` among all gains (`ex_10_4_err`, `ex_10_4_gain`,
  `ex_10_4`). The "equivalent" second form `x_{t+1} = Ax_t + Bu_t + Cε_t`,
  `y_t = Gx_t + Hu_{t−1} + Dε_t` is the first form after re-dating the shock and the observation,
  but with `Hu_{t−1}` in place of `Hu_t` (`ex_10_4_equiv`); the control term does not affect the
  filter covariances.
* **Exercise 10.5**: the representation (10.3)–(10.4) is the system (10.1)–(10.2) with `B = 0` and
  the known measurement input `h_t = Hz_t`; the filter is `x̂_{t+1|t} = Ax̂_{t|t−1} +
  AK_t(y_t − Gx̂_{t|t−1} − Hz_t)` with the covariances of `KFFilter` (`ex_10_5`). The book's
  assumption that `z_t` is independent of `x_s, ε_s` (`s ≥ t`) is not needed: the estimation error
  does not depend on `z`.
-/

open Filter Topology Matrix MeasureTheory

open scoped MatrixOrder

namespace Miao.PartialInformation

/-! ### Exercise 10.1 -/

/-- **Exercise 10.1** (Miao, p. 345): `y_t = μ + ε_t + bε_{t−1}` has the state-space form
`x_{t+1} = Ax_t + Cε_{t+1}`, `y_t = Gx_t + Hz_t` with `x_t = (ε_t, ε_{t−1})'`, `z_t = 1`,
`A = [0 0; 1 0]`, `C = (1, 0)'`, `G = [1 b]`, `H = μ`, `D = 0`. -/
theorem ex_10_1 (m b : ℝ) (ε y : ℤ → ℝ) (hy : ∀ t, y t = m + ε t + b * ε (t - 1)) (t : ℤ) :
    ![ε (t + 1), ε (t + 1 - 1)] = !![0, 0; 1, 0] *ᵥ ![ε t, ε (t - 1)] +
      !![1; 0] *ᵥ ![ε (t + 1)] ∧
    (fun _ : Fin 1 => y t) = !![1, b] *ᵥ ![ε t, ε (t - 1)] + !![m] *ᵥ ![1] := by
  refine ⟨?_, ?_⟩
  · funext i
    fin_cases i <;> simp
  · funext i
    simp [hy]
    ring

/-! ### Exercise 10.2 -/

/-- Exercise 10.2 (Miao, p. 345): with `ρ` unknown, the transition `(ρ, z) ↦ (ρ, ρz)` of the state
`(ρ, z_t)` is not linear: no matrix `A` satisfies `A(ρ, z)' = (ρ, ρz)'` for all `ρ, z`. -/
theorem ex_10_2_nonlinear :
    ¬ ∃ A : Matrix (Fin 2) (Fin 2) ℝ, ∀ r z : ℝ, A *ᵥ ![r, z] = ![r, r * z] := by
  rintro ⟨A, hA⟩
  have h1 := congrFun (hA 1 1) 1
  have h2 := congrFun (hA 2 2) 1
  simp [mulVec, dotProduct, Fin.sum_univ_two] at h1 h2
  linarith

/-- **Exercise 10.2** (Miao, p. 345), the Kalman filter conditional on `ρ`: for Example 10.1.1 with
`α = β = 0` (`z_{t+1} = ρz_t + σ_ηe¹_{t+1}`, `y_t = z_t + σ_ve²_t`), `Σ_{t+1|t} =
ρ²σ_v²Σ_{t|t−1}/(Σ_{t|t−1} + σ_v²) + σ_η²`, `K_t = Σ_{t|t−1}/(Σ_{t|t−1} + σ_v²)`,
`ẑ_{t+1|t} = ρẑ_{t|t−1} + ρK_t(y_t − ẑ_{t|t−1})`, and for `σ_η ≠ 0` the covariances converge to
the positive root `kf_scalarRoot (ρ²) σ_v² σ_η²`. -/
theorem ex_10_2 (ρ ση σv xbar0 s0 : ℝ) (hη : ση ≠ 0) (hv : σv ≠ 0) (hs0 : 0 ≤ s0) {Ω : Type*}
    (y : ℕ → Ω → Fin 1 → ℝ) (u : ℕ → Ω → Fin 1 → ℝ) :
    (∀ t, (kf_scalarSys ρ ση σv xbar0 s0).Spred (t + 1) 0 0 =
        kf_scalarRic (ρ ^ 2) (σv ^ 2) (ση ^ 2) ((kf_scalarSys ρ ση σv xbar0 s0).Spred t 0 0) ∧
      (kf_scalarSys ρ ση σv xbar0 s0).K t 0 0 = (kf_scalarSys ρ ση σv xbar0 s0).Spred t 0 0 /
        ((kf_scalarSys ρ ση σv xbar0 s0).Spred t 0 0 + σv ^ 2)) ∧
    (∀ t ω, (kf_scalarSys ρ ση σv xbar0 s0).xpred y 0 u (t + 1) ω 0 =
      ρ * (kf_scalarSys ρ ση σv xbar0 s0).xpred y 0 u t ω 0 +
        ρ * (kf_scalarSys ρ ση σv xbar0 s0).K t 0 0 *
          (y t ω 0 - (kf_scalarSys ρ ση σv xbar0 s0).xpred y 0 u t ω 0)) ∧
    Tendsto (fun t => (kf_scalarSys ρ ση σv xbar0 s0).Spred t 0 0) atTop
      (𝓝 (kf_scalarRoot (ρ ^ 2) (σv ^ 2) (ση ^ 2))) := by
  have hF := fun t => kf_scalar_filter ρ ση σv xbar0 s0 hv hs0 t
  refine ⟨fun t => ⟨(hF t).2.1, (hF t).2.2.1⟩, fun t ω => kf_scalar_xpred _ _ _ _ _ y u t ω, ?_⟩
  have hv2 : 0 < σv ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hv))
  have hη2 : 0 < ση ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hη))
  have h := (kf_scalar_tendsto (sq_nonneg ρ) hv2 hη2).2.2.2
    ((kf_scalarSys ρ ση σv xbar0 s0).Spred 0 0 0) (hF 0).1
  refine h.congr fun t => ?_
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', ih, ← (hF t).2.1]

/-! ### Exercise 10.3 -/

/-- **Exercise 10.3** (Miao, p. 345): `x_t = θ`, `y_t = θ + v_t`, `θ ∼ (μ, Σ₀)`, `Ev² = R > 0`
(the scalar system with `a = 1`, `c = 0`, `d = √R`). Then `Σ_{t|t−1} = Σ₀R/(R + tΣ₀)`,
`K_t = Σ₀/(R + (t + 1)Σ₀)`, the estimate is `x̂_{t|t−1} = (Rμ + Σ₀∑_{s<t}y_s)/(R + tΣ₀)`, and in the
long run `Σ_{t|t−1} → 0` and `K_t → 0`. -/
theorem ex_10_3 {R : ℝ} (hR : 0 < R) (m s0 : ℝ) (hs0 : 0 ≤ s0) {Ω : Type*}
    (y : ℕ → Ω → Fin 1 → ℝ) (u : ℕ → Ω → Fin 1 → ℝ) :
    (∀ t : ℕ, (kf_scalarSys 1 0 (Real.sqrt R) m s0).Spred t 0 0 = s0 * R / (R + t * s0)) ∧
      (∀ t : ℕ, (kf_scalarSys 1 0 (Real.sqrt R) m s0).K t 0 0 = s0 / (R + (t + 1) * s0)) ∧
      (∀ (t : ℕ) ω, (kf_scalarSys 1 0 (Real.sqrt R) m s0).xpred y 0 u t ω 0 =
        (R * m + s0 * ∑ s ∈ Finset.range t, y s ω 0) / (R + t * s0)) ∧
      Tendsto (fun t => (kf_scalarSys 1 0 (Real.sqrt R) m s0).Spred t 0 0) atTop (𝓝 0) ∧
      Tendsto (fun t => (kf_scalarSys 1 0 (Real.sqrt R) m s0).K t 0 0) atTop (𝓝 0) := by
  set S := kf_scalarSys 1 0 (Real.sqrt R) m s0
  have hd : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hF := fun t => kf_scalar_filter 1 0 (Real.sqrt R) m s0 hd hs0 t
  have hden : ∀ t : ℕ, 0 < R + t * s0 := fun t => by positivity
  have hP : ∀ t : ℕ, S.Spred t 0 0 = s0 * R / (R + t * s0) := by
    intro t
    induction t with
    | zero =>
      change (!![s0] : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = _
      simp only [of_apply, cons_val', empty_val', cons_val_fin_one, Nat.cast_zero, zero_mul,
        add_zero]
      field_simp
    | succ t ih =>
      rw [(hF t).2.1, hR2, ih, kf_scalarRic]
      have h1 := hden t
      have h2 := hden (t + 1)
      push_cast at h2 ⊢
      field_simp
      ring
  have hK : ∀ t : ℕ, S.K t 0 0 = s0 / (R + (t + 1) * s0) := by
    intro t
    rw [(hF t).2.2.1, hR2, hP]
    have h1 := hden t
    have h2 : 0 < R + (t + 1) * s0 := by positivity
    field_simp
    ring
  have hlim : ∀ k : ℝ, 0 ≤ k → ∀ c : ℝ,
      Tendsto (fun t : ℕ => c * s0 / (R + (t + k) * s0)) atTop (𝓝 0) := by
    intro k hk c
    rcases hs0.eq_or_lt with h0 | hpos
    · simp [← h0]
    · have h1 : Tendsto (fun t : ℕ => R + ((t : ℝ) + k) * s0) atTop atTop := by
        refine tendsto_atTop_add_const_left _ R ?_
        refine Tendsto.atTop_mul_const hpos ?_
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      exact Tendsto.div_atTop tendsto_const_nhds h1
  refine ⟨hP, hK, fun t ω => ?_, ?_, ?_⟩
  · induction t with
    | zero =>
      change S.xbar0 0 = _
      simp only [S, kf_scalarSys, KFSystem.const, Finset.range_zero, Finset.sum_empty, mul_zero,
        add_zero, Nat.cast_zero, zero_mul]
      field_simp
    | succ t ih =>
      rw [kf_scalar_xpred, ih, hK, Finset.sum_range_succ]
      have h1 := hden t
      have h2 : 0 < R + (t + 1) * s0 := by positivity
      push_cast
      field_simp
      ring
  · refine (hlim 0 le_rfl R).congr fun t => ?_
    rw [hP, add_zero, mul_comm R]
  · refine (hlim 1 zero_le_one 1).congr fun t => ?_
    rw [hK, one_mul]

/-- **Exercise 10.3** (Miao, p. 345), "what happens in the long run": under the hypotheses of
`KFSystem.kf_moments`, the mean squared error of the filtered estimate,
`E(θ − x̂_{t|t})² = Σ_{t|t}`, tends to `0` (the estimate converges to `θ` in mean square). -/
theorem ex_10_3_mse {R : ℝ} (hR : 0 < R) (m s0 : ℝ) (hs0 : 0 ≤ s0) {Ω : Type*}
    {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {x : ℕ → Ω → Fin 1 → ℝ} {y : ℕ → Ω → Fin 1 → ℝ} {u : ℕ → Ω → Fin 1 → ℝ}
    {ε : ℕ → Ω → Fin 2 → ℝ}
    (hx : ∀ t, x (t + 1) = kf_app ((kf_scalarSys 1 0 (Real.sqrt R) m s0).A t) (x t) +
      kf_app ((kf_scalarSys 1 0 (Real.sqrt R) m s0).B t) (u t) +
      kf_app ((kf_scalarSys 1 0 (Real.sqrt R) m s0).C t) (ε (t + 1)))
    (hy : ∀ t, y t = kf_app ((kf_scalarSys 1 0 (Real.sqrt R) m s0).G t) (x t) +
      (0 : ℕ → Ω → Fin 1 → ℝ) t +
      kf_app ((kf_scalarSys 1 0 (Real.sqrt R) m s0).D t) (ε t))
    (hL0 : kf_L2 μ (x 0)) (hLε : ∀ t, kf_L2 μ (ε t))
    (hm0 : kf_mean μ (x 0) = (kf_scalarSys 1 0 (Real.sqrt R) m s0).xbar0)
    (hmε : ∀ t, kf_mean μ (ε t) = 0)
    (hS0 : var_mom μ (x 0 - fun _ => (kf_scalarSys 1 0 (Real.sqrt R) m s0).xbar0)
      (x 0 - fun _ => (kf_scalarSys 1 0 (Real.sqrt R) m s0).xbar0) =
      (kf_scalarSys 1 0 (Real.sqrt R) m s0).S0)
    (hεε : ∀ s t, var_mom μ (ε s) (ε t) = if s = t then 1 else 0)
    (h0ε : ∀ t, var_mom μ (x 0 - fun _ => (kf_scalarSys 1 0 (Real.sqrt R) m s0).xbar0)
      (ε t) = 0) :
    Tendsto (fun t => var_mom μ (x t - (kf_scalarSys 1 0 (Real.sqrt R) m s0).xfilt y 0 u t)
      (x t - (kf_scalarSys 1 0 (Real.sqrt R) m s0).xfilt y 0 u t) 0 0) atTop (𝓝 0) := by
  set S := kf_scalarSys 1 0 (Real.sqrt R) m s0
  have hd : Real.sqrt R ≠ 0 := (Real.sqrt_pos.2 hR).ne'
  have hF := fun t => kf_scalar_filter 1 0 (Real.sqrt R) m s0 hd hs0 t
  have hΩ : ∀ t, IsUnit (S.Om t).det := by
    intro t
    rw [det_fin_one, (hF t).2.2.2, isUnit_iff_ne_zero]
    have := (hF t).1
    have : 0 < Real.sqrt R ^ 2 := by positivity
    linarith
  have hlim := ((ex_10_3 hR m s0 hs0 (fun _ _ _ => (0 : ℝ)) u).2.2.2.1).comp
    (tendsto_add_atTop_nat 1)
  refine hlim.congr fun t => ?_
  rw [Function.comp_apply, S.kf_filt_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ]
  change ((!![1] : Matrix (Fin 1) (Fin 1) ℝ) * S.Sfilt t * (!![1] : Matrix (Fin 1) (Fin 1) ℝ)ᵀ +
    (!![0, 0] : Matrix (Fin 1) (Fin 2) ℝ) * (!![0, 0] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ) 0 0 =
    S.Sfilt t 0 0
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero,
    transpose_apply, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, Fin.succ_zero_eq_one]
  ring

/-! ### Exercise 10.4 -/

variable {X U Y E : Type*} [Fintype X] [Fintype U] [Fintype Y] [Fintype E] [DecidableEq X]
  [DecidableEq Y]

/-- The dual LQ problem of Exercise 10.4: `(A', G', C, CC', DD', CD', 1)`. -/
def kf_ex4Dual (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ) (D : Matrix Y E ℝ) :
    LSProblem X Y E :=
  ⟨Aᵀ, Gᵀ, C, C * Cᵀ, D * Dᵀ, C * Dᵀ, 1⟩

/-- Exercise 10.4: the error covariances `Σ_0 = Σ₀`, `Σ_{t+1} = T̂(Σ_t)`. -/
noncomputable def kf_ex4Sig (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ)
    (D : Matrix Y E ℝ) (S0 : Matrix X X ℝ) : ℕ → Matrix X X ℝ
  | 0 => S0
  | t + 1 => (kf_ex4Dual A G C D).T (kf_ex4Sig A G C D S0 t)

/-- Exercise 10.4: the gains `K_t = F̂(Σ_t)'`. -/
noncomputable def kf_ex4Gain (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ)
    (D : Matrix Y E ℝ) (S0 : Matrix X X ℝ) (t : ℕ) : Matrix X Y ℝ :=
  ((kf_ex4Dual A G C D).F (kf_ex4Sig A G C D S0 t))ᵀ

/-- Exercise 10.4: the estimates `x̂_0 = x̄₀`,
`x̂_{t+1} = Ax̂_t + Bu_t + K_t(y_{t+1} − Gx̂_t − Hu_t)`. -/
noncomputable def kf_ex4Est {Ω : Type*} (A : Matrix X X ℝ) (B : Matrix X U ℝ) (G : Matrix Y X ℝ)
    (H : Matrix Y U ℝ) (K : ℕ → Matrix X Y ℝ) (xbar0 : X → ℝ) (y : ℕ → Ω → Y → ℝ)
    (u : ℕ → Ω → U → ℝ) : ℕ → Ω → X → ℝ
  | 0 => fun _ => xbar0
  | t + 1 => kf_app A (kf_ex4Est A B G H K xbar0 y u t) + kf_app B (u t) +
      kf_app (K t) (y (t + 1) - kf_app G (kf_ex4Est A B G H K xbar0 y u t) - kf_app H (u t))

omit [Fintype U] [DecidableEq X] in
/-- Exercise 10.4, the gain: for symmetric `Σ`, `F̂(Σ)' = (AΣG' + CD')(GΣG' + DD')⁻¹`. -/
theorem ex_10_4_gain (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ)
    (D : Matrix Y E ℝ) {P : Matrix X X ℝ} (hP : Pᵀ = P) :
    ((kf_ex4Dual A G C D).F P)ᵀ = (A * P * Gᵀ + C * Dᵀ) * (G * P * Gᵀ + D * Dᵀ)⁻¹ := by
  have hs : (G * P * Gᵀ + D * Dᵀ)ᵀ = G * P * Gᵀ + D * Dᵀ := by
    simp [transpose_add, transpose_mul, hP, Matrix.mul_assoc]
  simp only [LSProblem.F, LSProblem.G, LSProblem.N, kf_ex4Dual, one_smul, transpose_transpose,
    transpose_mul, transpose_add, transpose_nonsing_inv, hP]
  rw [add_comm (C * Dᵀ), add_comm (D * Dᵀ)]
  simp only [Matrix.mul_assoc]

omit [DecidableEq X] [DecidableEq Y] in
/-- Exercise 10.4, the error recursion: `x_{t+1} − x̂_{t+1} = (A − K_tG)(x_t − x̂_t) +
(C − K_tD)ε_{t+1}`. -/
theorem ex_10_4_err {Ω : Type*} (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ)
    (G : Matrix Y X ℝ) (H : Matrix Y U ℝ) (D : Matrix Y E ℝ) (K : ℕ → Matrix X Y ℝ)
    (xbar0 : X → ℝ) {x : ℕ → Ω → X → ℝ} {y : ℕ → Ω → Y → ℝ} {u : ℕ → Ω → U → ℝ}
    {ε : ℕ → Ω → E → ℝ}
    (hx : ∀ t, x (t + 1) = kf_app A (x t) + kf_app B (u t) + kf_app C (ε (t + 1)))
    (hy : ∀ t, y (t + 1) = kf_app G (x t) + kf_app H (u t) + kf_app D (ε (t + 1))) (t : ℕ) :
    x (t + 1) - kf_ex4Est A B G H K xbar0 y u (t + 1) =
      kf_app (A - K t * G) (x t - kf_ex4Est A B G H K xbar0 y u t) +
        kf_app (C - K t * D) (ε (t + 1)) := by
  funext ω
  simp only [kf_ex4Est, hx, hy, kf_app, Pi.add_apply, Pi.sub_apply, sub_mulVec, mulVec_add,
    mulVec_sub, mulVec_mulVec]
  abel

omit [Fintype U] [DecidableEq X] [DecidableEq Y] in
/-- The second moments of `Me + Nn` when `e` and `n` are uncorrelated and `Enn' = I`. -/
theorem kf_mom_two {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [DecidableEq E]
    {e : Ω → X → ℝ} {n : Ω → E → ℝ} (he : kf_L2 μ e) (hn : kf_L2 μ n) (M : Matrix X X ℝ)
    (N : Matrix X E ℝ) (hen : var_mom μ e n = 0) (hnn : var_mom μ n n = 1) :
    var_mom μ (kf_app M e + kf_app N n) (kf_app M e + kf_app N n) =
      M * var_mom μ e e * Mᵀ + N * Nᵀ := by
  have hw := kf_L2_add (kf_L2_app he M) (kf_L2_app hn N)
  have hsym : (var_mom μ e e)ᵀ = var_mom μ e e := (kf_mom_transpose e e).symm
  rw [kf_mom_lin2 he hn hw, kf_mom_transpose (kf_app M e + kf_app N n) e,
    kf_mom_transpose (kf_app M e + kf_app N n) n, kf_mom_lin2 he hn he, kf_mom_lin2 he hn hn,
    kf_mom_transpose e n, hen, hnn]
  simp [transpose_mul, hsym, Matrix.mul_assoc]

omit [Fintype U] [DecidableEq X] [DecidableEq Y] in
/-- The one-step covariance of Exercise 10.4 for an arbitrary gain `K` is the policy map (9.9) of
the dual problem: `(A − KG)Σ(A − KG)' + (C − KD)(C − KD)' = T̂_{K'}(Σ)`. -/
theorem kf_ex4_TF (A : Matrix X X ℝ) (G : Matrix Y X ℝ) (C : Matrix X E ℝ) (D : Matrix Y E ℝ)
    (P : Matrix X X ℝ) (K : Matrix X Y ℝ) :
    (A - K * G) * P * (A - K * G)ᵀ + (C - K * D) * (C - K * D)ᵀ =
      (kf_ex4Dual A G C D).TF P Kᵀ := by
  simp only [LSProblem.TF, kf_ex4Dual, one_smul, transpose_transpose, transpose_sub,
    transpose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

omit [DecidableEq X] in
/-- **Exercise 10.4** (Miao, p. 345). For `x_{t+1} = Ax_t + Bu_t + Cε_{t+1}`,
`y_{t+1} = Gx_t + Hu_t + Dε_{t+1}` (`x₀` with mean `x̄₀`, covariance `Σ₀`, uncorrelated with the
shocks; `DD' > 0`), the filter `x̂_{t+1} = Ax̂_t + Bu_t + K_t(y_{t+1} − Gx̂_t − Hu_t)` with
`K_t = (AΣ_tG' + CD')(GΣ_tG' + DD')⁻¹` (`ex_10_4_gain`) and `Σ_{t+1} = T̂(Σ_t) =
AΣ_tA' + CC' − (AΣ_tG' + CD')(GΣ_tG' + DD')⁻¹(GΣ_tA' + DC')` has: errors `x_t − x̂_t` with mean
zero, second moments `Σ_t`, uncorrelated with future shocks; and for every gain `K'` the error
second moments of `Ax̂_t + Bu_t + K'(y_{t+1} − Gx̂_t − Hu_t)` are `T̂_{K'}(Σ_t) ≥ Σ_{t+1}`. -/
theorem ex_10_4 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    [DecidableEq E] (A : Matrix X X ℝ) (B : Matrix X U ℝ) (C : Matrix X E ℝ) (G : Matrix Y X ℝ)
    (H : Matrix Y U ℝ) (D : Matrix Y E ℝ) (xbar0 : X → ℝ) (S0 : Matrix X X ℝ)
    (hR : (D * Dᵀ).PosDef) {x : ℕ → Ω → X → ℝ} {y : ℕ → Ω → Y → ℝ} {u : ℕ → Ω → U → ℝ}
    {ε : ℕ → Ω → E → ℝ}
    (hx : ∀ t, x (t + 1) = kf_app A (x t) + kf_app B (u t) + kf_app C (ε (t + 1)))
    (hy : ∀ t, y (t + 1) = kf_app G (x t) + kf_app H (u t) + kf_app D (ε (t + 1)))
    (hL0 : kf_L2 μ (x 0)) (hLε : ∀ t, kf_L2 μ (ε t)) (hm0 : kf_mean μ (x 0) = xbar0)
    (hmε : ∀ t, kf_mean μ (ε t) = 0)
    (hS0 : var_mom μ (x 0 - fun _ => xbar0) (x 0 - fun _ => xbar0) = S0)
    (hεε : ∀ s t, var_mom μ (ε s) (ε t) = if s = t then 1 else 0)
    (h0ε : ∀ t, var_mom μ (x 0 - fun _ => xbar0) (ε t) = 0) (t : ℕ) :
    let e := fun t => x t - kf_ex4Est A B G H (kf_ex4Gain A G C D S0) xbar0 y u t
    kf_L2 μ (e t) ∧ kf_mean μ (e t) = 0 ∧ var_mom μ (e t) (e t) = kf_ex4Sig A G C D S0 t ∧
      (∀ s, t < s → var_mom μ (e t) (ε s) = 0) ∧
      ∀ K' : Matrix X Y ℝ, kf_ex4Sig A G C D S0 (t + 1) ≤
        var_mom μ (kf_app (A - K' * G) (e t) + kf_app (C - K' * D) (ε (t + 1)))
          (kf_app (A - K' * G) (e t) + kf_app (C - K' * D) (ε (t + 1))) := by
  intro e
  set L := kf_ex4Dual A G C D
  have hRs : L.Rᵀ = L.R := by simp [L, kf_ex4Dual, transpose_mul]
  have hnn : var_mom μ (ε (t + 1)) (ε (t + 1)) = 1 := by rw [hεε]; simp
  have main : ∀ t, kf_L2 μ (e t) ∧ kf_mean μ (e t) = 0 ∧
      var_mom μ (e t) (e t) = kf_ex4Sig A G C D S0 t ∧
      ∀ s, t < s → var_mom μ (e t) (ε s) = 0 := by
    intro t
    induction t with
    | zero =>
      refine ⟨kf_L2_sub hL0 (kf_L2_const _), ?_, hS0, fun s _ => h0ε s⟩
      change kf_mean μ (x 0 - fun _ => xbar0) = 0
      rw [kf_mean_sub hL0 (kf_L2_const _), hm0, kf_mean_const, sub_self]
    | succ t ih =>
      obtain ⟨he, hme, hee, hes⟩ := ih
      have hrec : e (t + 1) = kf_app (A - kf_ex4Gain A G C D S0 t * G) (e t) +
          kf_app (C - kf_ex4Gain A G C D S0 t * D) (ε (t + 1)) :=
        ex_10_4_err A B C G H D _ xbar0 hx hy t
      have hPsd : (kf_ex4Sig A G C D S0 t).PosSemidef := by rw [← hee]; exact kf_mom_self_psd he
      have hPs : (kf_ex4Sig A G C D S0 t)ᵀ = kf_ex4Sig A G C D S0 t :=
        (SS.LQProblem.posSemidef_iff_real.1 hPsd).1
      have hG := L.G_posDef hR hPsd zero_le_one
      rw [hrec]
      refine ⟨kf_L2_add (kf_L2_app he _) (kf_L2_app (hLε _) _), ?_, ?_, fun s hs => ?_⟩
      · rw [kf_mean_add (kf_L2_app he _) (kf_L2_app (hLε _) _), kf_mean_app he,
          kf_mean_app (hLε _), hme, hmε]
        simp
      · rw [kf_mom_two he (hLε _) _ _ (hes _ (Nat.lt_succ_self t)) (by rw [hεε]; simp), hee,
          kf_ex4_TF, kf_ex4Gain, transpose_transpose,
          L.TF_F ((isUnit_iff_isUnit_det _).1 hG.isUnit)]
        rfl
      · rw [kf_mom_lin2 he (hLε _) (hLε s), hes s (by omega), hεε]
        have h1 : t + 1 ≠ s := by omega
        simp [h1]
  obtain ⟨he, -, hee, hes⟩ := main t
  refine ⟨he, (main t).2.1, hee, hes, fun K' => ?_⟩
  have hPsd : (kf_ex4Sig A G C D S0 t).PosSemidef := by rw [← hee]; exact kf_mom_self_psd he
  have hPs : (kf_ex4Sig A G C D S0 t)ᵀ = kf_ex4Sig A G C D S0 t :=
    (SS.LQProblem.posSemidef_iff_real.1 hPsd).1
  rw [kf_mom_two he (hLε _) _ _ (hes _ (Nat.lt_succ_self t)) hnn, hee, kf_ex4_TF]
  exact L.TF_ge_T hRs hPs (L.G_posDef hR hPsd zero_le_one) K'ᵀ

omit [Fintype X] [Fintype U] [Fintype Y] [Fintype E] [DecidableEq X] [DecidableEq Y] in
/-- Exercise 10.4 (Miao, pp. 345–346), the second form `x_{t+1} = Ax_t + Bu_t + Cε_t`,
`y_t = Gx_t + Hu_{t−1} + Dε_t`: with the re-dated shock `ε'_{t+1} = ε_t` and observation
`y'_{t+1} = y_t` it reads `x_{t+1} = Ax_t + Bu_t + Cε'_{t+1}`, `y'_{t+2} = Gx_{t+1} + Hu_t +
Dε'_{t+2}`, i.e. the first form with `Hu_t` replaced by `Hu_{t−1}`. -/
theorem ex_10_4_equiv [Fintype X] [Fintype U] [Fintype E] (A : Matrix X X ℝ)
    (B : Matrix X U ℝ) (C : Matrix X E ℝ) (G : Matrix Y X ℝ) (H : Matrix Y U ℝ)
    (D : Matrix Y E ℝ) (x : ℕ → X → ℝ) (y : ℕ → Y → ℝ) (u : ℕ → U → ℝ) (ε : ℕ → E → ℝ)
    (hx : ∀ t, x (t + 1) = A *ᵥ x t + B *ᵥ u t + C *ᵥ ε t)
    (hy : ∀ t, y (t + 1) = G *ᵥ x (t + 1) + H *ᵥ u t + D *ᵥ ε (t + 1)) (t : ℕ) :
    let ε' := fun s => ε (s - 1)
    let y' := fun s => y (s - 1)
    x (t + 1) = A *ᵥ x t + B *ᵥ u t + C *ᵥ ε' (t + 1) ∧
      y' (t + 2) = G *ᵥ x (t + 1) + H *ᵥ u t + D *ᵥ ε' (t + 2) := by
  intro ε' y'
  exact ⟨hx t, hy t⟩

/-! ### Exercise 10.5 -/

/-- **Exercise 10.5** (Miao, p. 346): the Kalman filter for (10.3)–(10.4),
`x_{t+1} = Ax_t + Cε_{t+1}`, `y_t = Gx_t + Hz_t + Dε_t`. It is the filter of the system
(10.1)–(10.2) with `B = 0` and the known measurement input `h_t = Hz_t`:
`x̂_{t+1|t} = Ax̂_{t|t−1} + AK_ta_t`, `a_t = y_t − Gx̂_{t|t−1} − Hz_t`, `K_t = (Σ_{t|t−1}G' +
C_{t−1}D')Ω⁻¹`; the prediction errors have second moments `Σ_{t|t−1}` and the innovations
`Ω_{t|t−1}` (Step 2 of p. 332). -/
theorem ex_10_5 {Z : Type*} [Fintype Z] {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] [DecidableEq E] (A : Matrix X X ℝ) (C : Matrix X E ℝ)
    (G : Matrix Y X ℝ) (H : Matrix Y Z ℝ) (D : Matrix Y E ℝ) (xbar0 : X → ℝ)
    (S0 : Matrix X X ℝ) {x : ℕ → Ω → X → ℝ} {y : ℕ → Ω → Y → ℝ} {z : ℕ → Ω → Z → ℝ}
    {u : ℕ → Ω → U → ℝ} {ε : ℕ → Ω → E → ℝ}
    (hx : ∀ t, x (t + 1) = kf_app A (x t) + kf_app C (ε (t + 1)))
    (hy : ∀ t, y t = kf_app G (x t) + kf_app H (z t) + kf_app D (ε t))
    (hL0 : kf_L2 μ (x 0)) (hLε : ∀ t, kf_L2 μ (ε t)) (hm0 : kf_mean μ (x 0) = xbar0)
    (hmε : ∀ t, kf_mean μ (ε t) = 0)
    (hS0 : var_mom μ (x 0 - fun _ => xbar0) (x 0 - fun _ => xbar0) = S0)
    (hεε : ∀ s t, var_mom μ (ε s) (ε t) = if s = t then 1 else 0)
    (h0ε : ∀ t, var_mom μ (x 0 - fun _ => xbar0) (ε t) = 0)
    (hΩ : ∀ t, IsUnit ((KFSystem.const A (0 : Matrix X U ℝ) C G 0 D xbar0 S0).Om t).det)
    (t : ℕ) :
    let S := KFSystem.const A (0 : Matrix X U ℝ) C G 0 D xbar0 S0
    let h := fun t => kf_app H (z t)
    S.xpred y h u (t + 1) = kf_app A (S.xpred y h u t) +
        kf_app (A * S.K t) (y t - kf_app G (S.xpred y h u t) - h t) ∧
      var_mom μ (x t - S.xpred y h u t) (x t - S.xpred y h u t) = S.Spred t ∧
      var_mom μ (S.innov y h u t) (S.innov y h u t) = S.Om t := by
  intro S h
  have hx' : ∀ t, x (t + 1) = kf_app (S.A t) (x t) + kf_app (S.B t) (u t) +
      kf_app (S.C t) (ε (t + 1)) := by
    intro t
    rw [hx, show S.B t = 0 from rfl, kf_app_zero_mat, add_zero]
    rfl
  have hy' : ∀ t, y t = kf_app (S.G t) (x t) + h t + kf_app (S.D t) (ε t) := hy
  refine ⟨?_, (S.kf_moments μ hx' hy' hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t).2.2.1,
    (S.eq_10_8 μ hx' hy' hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t).1⟩
  rw [KFSystem.kf_pred_recursive, show S.B t = 0 from rfl, kf_app_zero_mat, add_zero]
  rfl

end Miao.PartialInformation
