/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PartialInformation.KFAlgebra

/-!
# The Kalman filter

Miao, §10.1.1, pp. 327–334. The linear state-space system (10.1)–(10.2)

* `x_{t+1} = A_tx_t + B_tu_t + C_tε_{t+1}` (state transition),
* `y_t = G_tx_t + H_{t−1}u_{t−1} + D_tε_t` (measurement)

with time-varying matrices (`KFSystem`), and the Kalman filter of Step 1–Step 3 (p. 332):
`x̂_{0|−1} = x̄₀`, `Σ_{0|−1} = Σ₀`, `a_t = y_t − G_tx̂_{t|t−1} − H_{t−1}u_{t−1}` (`innov`),
`x̂_{t|t} = x̂_{t|t−1} + K_ta_t` (10.7) (`xfilt`), `x̂_{t+1|t} = A_tx̂_{t|t} + B_tu_t` (`xpred`),
and
the deterministic covariance recursion `Σ_{t|t−1}` (`Spred`), `Ω_{t|t−1}` (`Om`), `K_t` (`K`),
`Σ_{t|t}` (`Sfilt`).

**Reading.** The filter is proved in its *linear-projection* (second-moment) version. The
probability space `(Ω, μ)` is arbitrary; the shocks are square integrable, mean zero, mutually
uncorrelated with `Eε_tε_t' = I`, and `x₀` has mean `x̄₀`, covariance `Σ₀` and is uncorrelated with
the shocks. No Gaussianity, no independence and no measurability of the controls is used: the
controls `u_t` and the measurement input (`h_t`, the book's `H_{t−1}u_{t−1}`, `inp`) are
arbitrary random vectors, because the estimation error does not depend on them
(`kf_err_control_free`). What is proved:

* the error recursion `x_{t+1} − x̂_{t+1|t} = A_t(x_t − x̂_{t|t}) + C_tε_{t+1}` with
  `a_t = G_t(x_t − x̂_{t|t−1}) + D_tε_t` (`kf_err_succ`, `kf_innov_eq`, (10.9) first line);
* `kf_moments`: `x_t − x̂_{t|t−1}` has mean zero and second moments `Σ_{t|t−1}`, and
  `E[(x_t − x̂_{t|t−1})ε_s'] = 0` for `s > t` and `= C_{t−1}` for `s = t` (10.9);
* (10.8) `Ea_ta_t' = Ω_{t|t−1}` (`eq_10_8`); `E(x_t − x̂_{t|t−1})a_t' = Σ_{t|t−1}G_t' + C_{t−1}D_t'`
  (`eq_10_12_cov`, the covariance in (10.12));
* (10.11) for an arbitrary gain (`eq_10_11`), the Kalman gain (10.10) is optimal
  (`eq_10_10_random`), and `E(x_t − x̂_{t|t})(x_t − x̂_{t|t})' = Σ_{t|t}` (`kf_filt_moments`);
* the projection property (10.12): the innovations have mean zero and are mutually uncorrelated
  (`kf_innov_orth`), the prediction error is orthogonal to all past innovations and the filtered
  error to all innovations up to `t` (`kf_err_orth`, `kf_filt_orth`), and
  `x̂_{t|t−1}` is the best predictor of `x_t` among all predictors `x̂_{t|t−1} + ∑_{s<t}L_sa_s + c`
  (`eq_10_12`): their error second moment is `Σ_{t|t−1} + ∑L_sΩ_sL_s' + cc'`.
* the fully recursive forms of p. 333 (`kf_pred_recursive`, `kf_filt_recursive`) and the Riccati
  equations (`kf_riccati_Spred`, `kf_riccati_Sfilt`).

**The Gaussian reading** (`x_t | F_t ∼ N(x̂_{t|t}, Σ_{t|t})`, innovations independent and
normal, conditional = unconditional covariances, p. 328 and p. 333) is not formalised; the
second-moment statements above are its content for the first two moments.

**Corrections.** (i) The cross covariance is `E[(x_t − x̂_{t|t−1})ε_t'] = C_{t−1}` (the loading of
`ε_t` in `x_t = A_{t−1}x_{t−1} + B_{t−1}u_{t−1} + C_{t−1}ε_t`), not `C_t` as printed in (10.9),
and it is `0` at `t = 0` (the initialisation `x₀ ∼ N(x̄₀, Σ₀)` is independent of `ε₀`). So the
`C_t` in (10.8), (10.10), (10.11), the formula for `Σ_{t|t}` and the Riccati equations of
p. 333 is `C_{t−1}` (`Cl t`), which matters when `C_t` varies or at `t = 0`
(`eq_10_9`; counterexample at `t = 0`: `kf_cross_book_false`). (ii) The simplification of
(10.11) to `Σ_{t|t} = (I − KG)Σ_{t|t−1} − KDC'` needs `Ω_{t|t−1}` invertible (assumed: `hΩ`).
-/

open MeasureTheory Matrix

open scoped MatrixOrder

namespace Miao.PartialInformation

/-- The state-space system (10.1)–(10.2) (Miao, pp. 327–328): `x_{t+1} = A_tx_t + B_tu_t +
C_tε_{t+1}`, `y_t = G_tx_t + H_{t−1}u_{t−1} + D_tε_t`, `x₀` with mean `x̄₀` and covariance `Σ₀`. -/
structure KFSystem (X U Y E : Type*) where
  /-- the state transition matrices `A_t` -/
  A : ℕ → Matrix X X ℝ
  /-- the control matrices `B_t` -/
  B : ℕ → Matrix X U ℝ
  /-- the state shock loadings `C_t` -/
  C : ℕ → Matrix X E ℝ
  /-- the measurement matrices `G_t` -/
  G : ℕ → Matrix Y X ℝ
  /-- the measurement control matrices `H_t` -/
  H : ℕ → Matrix Y U ℝ
  /-- the measurement shock loadings `D_t` -/
  D : ℕ → Matrix Y E ℝ
  /-- the mean `x̄₀` of `x₀` -/
  xbar0 : X → ℝ
  /-- the covariance `Σ₀` of `x₀` -/
  S0 : Matrix X X ℝ

namespace KFSystem

variable {X U Y E : Type*} [Fintype X] [Fintype U] [Fintype Y] [Fintype E] [DecidableEq X]
  [DecidableEq Y] (S : KFSystem X U Y E)

/-- The cross covariance `E[(x_t − x̂_{t|t−1})ε_t']`: `0` at `t = 0`, `C_{t−1}` for `t ≥ 1`
(the book's (10.9), corrected). -/
def Cl : ℕ → Matrix X E ℝ
  | 0 => 0
  | t + 1 => S.C t

/-- The predicted covariances `Σ_{t|t−1}` (Step 1–Step 3, Miao, pp. 332–333): `Σ_{0|−1} = Σ₀`,
`Σ_{t+1|t} = A_tΣ_{t|t}A_t' + C_tC_t'`. -/
noncomputable def Spred : ℕ → Matrix X X ℝ
  | 0 => S.S0
  | t + 1 => S.A t * kf_filtCov (S.G t) (S.D t) (S.Cl t) (Spred t) * (S.A t)ᵀ + S.C t * (S.C t)ᵀ

/-- (10.8): `Ω_{t|t−1}`. -/
noncomputable def Om (t : ℕ) : Matrix Y Y ℝ := kf_Om (S.G t) (S.D t) (S.Cl t) (S.Spred t)

/-- (10.10): the Kalman gain `K_t`. -/
noncomputable def K (t : ℕ) : Matrix X Y ℝ := kf_gain (S.G t) (S.D t) (S.Cl t) (S.Spred t)

/-- The filtered covariance `Σ_{t|t} = (I − K_tG_t)Σ_{t|t−1} − K_tD_tC_{t−1}'`. -/
noncomputable def Sfilt (t : ℕ) : Matrix X X ℝ :=
  kf_filtCov (S.G t) (S.D t) (S.Cl t) (S.Spred t)

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The measurement input of (10.2): `0` at `t = 0`, `H_{t−1}u_{t−1}` for `t ≥ 1`. -/
def inp (u : ℕ → Ω → U → ℝ) : ℕ → Ω → Y → ℝ
  | 0 => 0
  | t + 1 => kf_app (S.H t) (u t)

/-- The predictions `x̂_{t|t−1}` computed from the observations `y`, the known measurement input
`h` and the controls `u` (Step 1–Step 3, Miao, pp. 332–333). -/
noncomputable def xpred (y h : ℕ → Ω → Y → ℝ) (u : ℕ → Ω → U → ℝ) : ℕ → Ω → X → ℝ
  | 0 => fun _ => S.xbar0
  | t + 1 => kf_app (S.A t) (xpred y h u t + kf_app (S.K t)
      (y t - kf_app (S.G t) (xpred y h u t) - h t)) + kf_app (S.B t) (u t)

/-- The innovation `a_t = y_t − ŷ_{t|t−1}`, `ŷ_{t|t−1} = G_tx̂_{t|t−1} + h_t`. -/
noncomputable def innov (y h : ℕ → Ω → Y → ℝ) (u : ℕ → Ω → U → ℝ) (t : ℕ) : Ω → Y → ℝ :=
  y t - kf_app (S.G t) (S.xpred y h u t) - h t

/-- (10.7): the filtered estimate `x̂_{t|t} = x̂_{t|t−1} + K_ta_t`. -/
noncomputable def xfilt (y h : ℕ → Ω → Y → ℝ) (u : ℕ → Ω → U → ℝ) (t : ℕ) : Ω → X → ℝ :=
  S.xpred y h u t + kf_app (S.K t) (S.innov y h u t)

/-- The prediction error `x_t − x̂_{t|t−1}`. -/
noncomputable def err (x : ℕ → Ω → X → ℝ) (y h : ℕ → Ω → Y → ℝ) (u : ℕ → Ω → U → ℝ) (t : ℕ) :
    Ω → X → ℝ :=
  x t - S.xpred y h u t

/-- Miao, p. 330: `x̂_{t+1|t} = A_tx̂_{t|t} + B_tu_t`. -/
theorem xpred_succ (y h : ℕ → Ω → Y → ℝ) (u : ℕ → Ω → U → ℝ) (t : ℕ) :
    S.xpred y h u (t + 1) = kf_app (S.A t) (S.xfilt y h u t) + kf_app (S.B t) (u t) := rfl

variable {x : ℕ → Ω → X → ℝ} {y h : ℕ → Ω → Y → ℝ} {u : ℕ → Ω → U → ℝ} {ε : ℕ → Ω → E → ℝ}

/-- The innovation in terms of the error (Miao, p. 330): `a_t = G_t(x_t − x̂_{t|t−1}) + D_tε_t`. -/
theorem kf_innov_eq (hy : ∀ t, y t = kf_app (S.G t) (x t) + h t + kf_app (S.D t) (ε t))
    (t : ℕ) : S.innov y h u t = kf_app (S.G t) (S.err x y h u t) + kf_app (S.D t) (ε t) := by
  rw [innov, hy, err, kf_app_sub]
  abel

/-- The error recursion (Miao, pp. 330 and 344): `x_{t+1} − x̂_{t+1|t} =
A_t(x_t − x̂_{t|t}) + C_tε_{t+1}`, with `x_t − x̂_{t|t} = (x_t − x̂_{t|t−1}) − K_ta_t`. -/
theorem kf_err_succ
    (hx : ∀ t, x (t + 1) = kf_app (S.A t) (x t) + kf_app (S.B t) (u t) +
      kf_app (S.C t) (ε (t + 1))) (t : ℕ) :
    S.err x y h u (t + 1) = kf_app (S.A t) (S.err x y h u t - kf_app (S.K t) (S.innov y h u t)) +
      kf_app (S.C t) (ε (t + 1)) := by
  rw [err, hx, xpred_succ, xfilt, err, kf_app_sub, kf_app_sub, kf_app_add]
  abel

theorem err_zero : S.err x y h u 0 = x 0 - fun _ => S.xbar0 := rfl

/-- Miao, p. 344: the estimation error does not depend on the controls (nor on the known
measurement input). Two control sequences `u, u'` with the same `x₀` and shocks give the same
prediction errors and the same innovations. -/
theorem kf_err_control_free {x' : ℕ → Ω → X → ℝ} {y' h' : ℕ → Ω → Y → ℝ} {u' : ℕ → Ω → U → ℝ}
    (hx : ∀ t, x (t + 1) = kf_app (S.A t) (x t) + kf_app (S.B t) (u t) +
      kf_app (S.C t) (ε (t + 1)))
    (hy : ∀ t, y t = kf_app (S.G t) (x t) + h t + kf_app (S.D t) (ε t))
    (hx' : ∀ t, x' (t + 1) = kf_app (S.A t) (x' t) + kf_app (S.B t) (u' t) +
      kf_app (S.C t) (ε (t + 1)))
    (hy' : ∀ t, y' t = kf_app (S.G t) (x' t) + h' t + kf_app (S.D t) (ε t))
    (h0 : x' 0 = x 0) (t : ℕ) :
    S.err x' y' h' u' t = S.err x y h u t ∧ S.innov y' h' u' t = S.innov y h u t := by
  have he : ∀ t, S.err x' y' h' u' t = S.err x y h u t := by
    intro t
    induction t with
    | zero => rw [err_zero, err_zero, h0]
    | succ t ih =>
      rw [S.kf_err_succ hx', S.kf_err_succ hx, S.kf_innov_eq hy', S.kf_innov_eq hy, ih]
  exact ⟨he t, by rw [S.kf_innov_eq hy', S.kf_innov_eq hy, he t]⟩

/-! ### Second moments -/

variable {μ : Measure Ω}

omit [Fintype U] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- One updating step in second moments. Let `e` (the prediction error), `c` (the current shock)
and `n` (the next shock) be square integrable with `Eee' = P`, `Eec' = Cℓ`, `Ecc' = Enn' = I`,
`Een' = Ecn' = 0`; let `a = Ge + Dc` and `f = e − Ka`. Then `Eaa' = Ω` (10.8), `Eea' = PG' + CℓD'`,
`Eff' = Σ(K)` (10.11), and `e' = Af + Cn` has `Ee'e' = AΣ(K)A' + CC'` and `Ee'n' = C`. -/
theorem kf_step {W : Type*} [Fintype W] [DecidableEq E] {e : Ω → X → ℝ}
    {c n : Ω → E → ℝ} {a : Ω → W → ℝ} {f : Ω → X → ℝ} (he : kf_L2 μ e) (hc : kf_L2 μ c)
    (hn : kf_L2 μ n) [DecidableEq X] (G : Matrix W X ℝ) (D : Matrix W E ℝ)
    (Cl : Matrix X E ℝ) (K : Matrix X W ℝ) (A : Matrix X X ℝ) (C : Matrix X E ℝ)
    {P : Matrix X X ℝ} (ha : a = kf_app G e + kf_app D c) (hf : f = e - kf_app K a)
    (hee : var_mom μ e e = P) (hec : var_mom μ e c = Cl) (hcc : var_mom μ c c = 1)
    (hen : var_mom μ e n = 0) (hcn : var_mom μ c n = 0) (hnn : var_mom μ n n = 1) :
    var_mom μ a a = kf_Om G D Cl P ∧ var_mom μ e a = kf_Mx G D Cl P ∧
      var_mom μ f a = kf_Mx G D Cl P - K * kf_Om G D Cl P ∧
      var_mom μ f f = kf_joseph G D Cl P K ∧
      var_mom μ (kf_app A f + kf_app C n) (kf_app A f + kf_app C n) =
        A * kf_joseph G D Cl P K * Aᵀ + C * Cᵀ ∧
      var_mom μ (kf_app A f + kf_app C n) n = C ∧ var_mom μ f n = 0 := by
  subst ha hf
  set a := kf_app G e + kf_app D c with ha
  set f := e - kf_app K a with hf
  have hP : Pᵀ = P := by rw [← hee, ← kf_mom_transpose]
  have ha2 : kf_L2 μ a := kf_L2_add (kf_L2_app he G) (kf_L2_app hc D)
  have hf2 : kf_L2 μ f := kf_L2_sub he (kf_L2_app ha2 K)
  have hce : var_mom μ c e = Clᵀ := by rw [kf_mom_transpose, hec]
  have hae : var_mom μ a e = G * P + D * Clᵀ := by rw [kf_mom_lin2 he hc he, hee, hce]
  have hac : var_mom μ a c = G * Cl + D := by rw [kf_mom_lin2 he hc hc, hec, hcc, Matrix.mul_one]
  have hea : var_mom μ e a = kf_Mx G D Cl P := by
    rw [kf_mom_transpose, hae, ← kf_Mx_transpose G D Cl hP, transpose_transpose]
  have haa : var_mom μ a a = kf_Om G D Cl P := by
    rw [kf_mom_lin2 he hc ha2, hea, kf_mom_transpose, hac]
    simp only [kf_Om, kf_Mx, transpose_add, transpose_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  have hfa : var_mom μ f a = kf_Mx G D Cl P - K * kf_Om G D Cl P := by
    rw [kf_mom_lin_sub he ha2 ha2, hea, haa]
  have hfe : var_mom μ f e = P - K * (kf_Mx G D Cl P)ᵀ := by
    rw [kf_mom_lin_sub he ha2 he, hee, hae, kf_Mx_transpose G D Cl hP]
  have hff : var_mom μ f f = kf_joseph G D Cl P K := by
    rw [kf_mom_lin_sub he ha2 hf2, kf_mom_transpose f e, hfe, kf_mom_transpose f a, hfa,
      kf_joseph_expand G D Cl hP]
    simp only [transpose_sub, transpose_mul, hP, transpose_transpose, Matrix.mul_sub,
      kf_Om_transpose G D Cl hP, Matrix.mul_assoc]
    abel
  have han : var_mom μ a n = 0 := by
    rw [kf_mom_lin2 he hc hn, hen, hcn, Matrix.mul_zero, Matrix.mul_zero,
      add_zero]
  have hfn : var_mom μ f n = 0 := by
    rw [kf_mom_lin_sub he ha2 hn, hen, han, Matrix.mul_zero, sub_zero]
  have hAf := kf_L2_app hf2 A
  have hCn := kf_L2_app hn C
  have hn' : var_mom μ (kf_app A f + kf_app C n) n = C := by
    rw [kf_mom_add_left hAf hCn hn, kf_mom_app_left hf2 hn, kf_mom_app_left hn hn, hfn, hnn,
      Matrix.mul_zero, zero_add, Matrix.mul_one]
  have hef : var_mom μ (kf_app A f + kf_app C n) f = A * kf_joseph G D Cl P K := by
    rw [kf_mom_add_left hAf hCn hf2, kf_mom_app_left hf2 hf2, kf_mom_app_left hn hf2, hff,
      kf_mom_transpose f n, hfn, transpose_zero, Matrix.mul_zero, add_zero]
  have hJ : (kf_joseph G D Cl P K)ᵀ = kf_joseph G D Cl P K := by
    rw [← hff, ← kf_mom_transpose]
  refine ⟨haa, hea, hfa, hff, ?_, hn', hfn⟩
  rw [kf_mom_add_left hAf hCn (kf_L2_add hAf hCn), kf_mom_app_left hf2 (kf_L2_add hAf hCn),
    kf_mom_app_left hn (kf_L2_add hAf hCn), kf_mom_transpose (kf_app A f + kf_app C n) f, hef,
    kf_mom_transpose (kf_app A f + kf_app C n) n, hn',
    transpose_mul, hJ, Matrix.mul_assoc]

variable (μ)

/-- The prediction errors and their second moments (Miao, pp. 330–333). Under (10.1)–(10.2),
for every `t`: `x_t − x̂_{t|t−1}` is square integrable with mean zero, its second-moment matrix is
`Σ_{t|t−1}`, and (10.9) `E[(x_t − x̂_{t|t−1})ε_s'] = C_{t−1}` for `s = t` (`0` at `t = 0`) and
`= 0` for `s > t`. -/
theorem kf_moments [IsProbabilityMeasure μ] [DecidableEq E]
    (hx : ∀ t, x (t + 1) = kf_app (S.A t) (x t) + kf_app (S.B t) (u t) +
      kf_app (S.C t) (ε (t + 1)))
    (hy : ∀ t, y t = kf_app (S.G t) (x t) + h t + kf_app (S.D t) (ε t))
    (hL0 : kf_L2 μ (x 0)) (hLε : ∀ t, kf_L2 μ (ε t)) (hm0 : kf_mean μ (x 0) = S.xbar0)
    (hmε : ∀ t, kf_mean μ (ε t) = 0)
    (hS0 : var_mom μ (x 0 - fun _ => S.xbar0) (x 0 - fun _ => S.xbar0) = S.S0)
    (hεε : ∀ s t, var_mom μ (ε s) (ε t) = if s = t then 1 else 0)
    (h0ε : ∀ t, var_mom μ (x 0 - fun _ => S.xbar0) (ε t) = 0)
    (hΩ : ∀ t, IsUnit (S.Om t).det) (t : ℕ) :
    kf_L2 μ (S.err x y h u t) ∧ kf_mean μ (S.err x y h u t) = 0 ∧
      var_mom μ (S.err x y h u t) (S.err x y h u t) = S.Spred t ∧
      ∀ s, t ≤ s → var_mom μ (S.err x y h u t) (ε s) = if s = t then S.Cl t else 0 := by
  induction t with
  | zero =>
    rw [err_zero]
    refine ⟨kf_L2_sub hL0 (kf_L2_const _), ?_, hS0, fun s _ => ?_⟩
    · rw [kf_mean_sub hL0 (kf_L2_const _), hm0, kf_mean_const, sub_self]
    · rw [h0ε]
      split_ifs <;> rfl
  | succ t ih =>
    obtain ⟨he, hme, hee, hes⟩ := ih
    have hεs : ∀ s, t + 1 ≤ s → var_mom μ (ε t) (ε s) = 0 := by
      intro s hs
      rw [hεε]
      simp only [ite_eq_right_iff]
      intro h
      omega
    have hes' : ∀ s, t + 1 ≤ s → var_mom μ (S.err x y h u t) (ε s) = 0 := by
      intro s hs
      rw [hes s (by omega)]
      simp only [ite_eq_right_iff]
      intro h
      omega
    obtain ⟨-, -, -, -, hmom, hcn, hfn⟩ := kf_step (μ := μ) he (hLε t) (hLε (t + 1)) (S.G t)
      (S.D t) (S.Cl t) (S.K t) (S.A t) (S.C t) (S.kf_innov_eq hy t) rfl hee
      (by rw [hes t le_rfl]; simp) (by rw [hεε]; simp) (hes' _ le_rfl)
      (hεs _ le_rfl) (by rw [hεε]; simp)
    have ha2 : kf_L2 μ (S.innov y h u t) := by
      rw [S.kf_innov_eq hy]; exact kf_L2_add (kf_L2_app he _) (kf_L2_app (hLε t) _)
    have hf2 : kf_L2 μ (S.err x y h u t - kf_app (S.K t) (S.innov y h u t)) :=
      kf_L2_sub he (kf_L2_app ha2 _)
    rw [S.kf_err_succ hx]
    refine ⟨kf_L2_add (kf_L2_app hf2 _) (kf_L2_app (hLε _) _), ?_, ?_, fun s hs => ?_⟩
    · rw [kf_mean_add (kf_L2_app hf2 _) (kf_L2_app (hLε _) _), kf_mean_app hf2,
        kf_mean_app (hLε _), kf_mean_sub he (kf_L2_app ha2 _), kf_mean_app ha2,
        S.kf_innov_eq hy, kf_mean_add (kf_L2_app he _) (kf_L2_app (hLε _) _), kf_mean_app he,
        kf_mean_app (hLε _), hme, hmε, hmε]
      simp
    · have hPs : (S.Spred t)ᵀ = S.Spred t := by rw [← hee, ← kf_mom_transpose]
      rw [hmom, show S.K t = kf_gain (S.G t) (S.D t) (S.Cl t) (S.Spred t) from rfl,
        eq_10_11_gain (P := S.Spred t) _ _ _ hPs (hΩ t)]
      rfl
    · rcases eq_or_lt_of_le hs with hst | hst
      · subst hst
        rw [hcn]
        simp only [↓reduceIte]
        rfl
      · have hfs : var_mom μ (S.err x y h u t - kf_app (S.K t) (S.innov y h u t)) (ε s) = 0 := by
          rw [kf_mom_sub_left he (kf_L2_app ha2 _) (hLε s), kf_mom_app_left ha2 (hLε s),
            S.kf_innov_eq hy, kf_mom_add_left (kf_L2_app he _) (kf_L2_app (hLε t) _) (hLε s),
            kf_mom_app_left he (hLε s), kf_mom_app_left (hLε t) (hLε s), hes' s (by omega),
            hεs s (by omega)]
          simp
        rw [kf_mom_add_left (kf_L2_app hf2 _) (kf_L2_app (hLε _) _) (hLε s),
          kf_mom_app_left hf2 (hLε s), kf_mom_app_left (hLε _) (hLε s), hfs, hεε]
        have h1 : t + 1 ≠ s := by omega
        have h2 : s ≠ t + 1 := by omega
        simp [h1, h2]

/-! ### Consequences under the model hypotheses -/

variable [IsProbabilityMeasure μ] [DecidableEq E]
  (hx : ∀ t, x (t + 1) = kf_app (S.A t) (x t) + kf_app (S.B t) (u t) +
    kf_app (S.C t) (ε (t + 1)))
  (hy : ∀ t, y t = kf_app (S.G t) (x t) + h t + kf_app (S.D t) (ε t))
  (hL0 : kf_L2 μ (x 0)) (hLε : ∀ t, kf_L2 μ (ε t)) (hm0 : kf_mean μ (x 0) = S.xbar0)
  (hmε : ∀ t, kf_mean μ (ε t) = 0)
  (hS0 : var_mom μ (x 0 - fun _ => S.xbar0) (x 0 - fun _ => S.xbar0) = S.S0)
  (hεε : ∀ s t, var_mom μ (ε s) (ε t) = if s = t then 1 else 0)
  (h0ε : ∀ t, var_mom μ (x 0 - fun _ => S.xbar0) (ε t) = 0)
  (hΩ : ∀ t, IsUnit (S.Om t).det)

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- The innovations are square integrable with mean zero. -/
theorem kf_innov_L2 (t : ℕ) :
    kf_L2 μ (S.innov y h u t) ∧ kf_mean μ (S.innov y h u t) = 0 := by
  obtain ⟨he, hme, -, -⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  rw [S.kf_innov_eq hy]
  refine ⟨kf_L2_add (kf_L2_app he _) (kf_L2_app (hLε t) _), ?_⟩
  rw [kf_mean_add (kf_L2_app he _) (kf_L2_app (hLε t) _), kf_mean_app he, kf_mean_app (hLε t),
    hme, hmε]
  simp

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- **(10.9)** (Miao, p. 330), corrected: `E[(x_t − x̂_{t|t−1})ε_t'] = C_{t−1}` (`0` at
`t = 0`). -/
theorem eq_10_9 (t : ℕ) : var_mom μ (S.err x y h u t) (ε t) = S.Cl t := by
  obtain ⟨-, -, -, hes⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  rw [hes t le_rfl]
  simp

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- **(10.8)** (Miao, p. 330) and the covariances of (10.12) (p. 332): `Ea_ta_t' = Ω_{t|t−1}`,
`E[(x_t − x̂_{t|t−1})a_t'] = Σ_{t|t−1}G_t' + C_{t−1}D_t'`. -/
theorem eq_10_8 (t : ℕ) :
    var_mom μ (S.innov y h u t) (S.innov y h u t) = S.Om t ∧
      var_mom μ (S.err x y h u t) (S.innov y h u t) =
        kf_Mx (S.G t) (S.D t) (S.Cl t) (S.Spred t) := by
  obtain ⟨he, -, hee, hes⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  obtain ⟨haa, hea, -⟩ := kf_step (μ := μ) he (hLε t) (hLε (t + 1)) (S.G t) (S.D t) (S.Cl t)
    (S.K t) (S.A t) (S.C t) (S.kf_innov_eq hy t) rfl hee (by rw [hes t le_rfl]; simp)
    (by rw [hεε]; simp) (by rw [hes _ (Nat.le_succ t)]; simp) (by rw [hεε]; simp)
    (by rw [hεε]; simp)
  exact ⟨haa, hea⟩

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- **(10.11)** (Miao, p. 331): for an arbitrary gain `K'`, the error of the update
`x̂_{t|t−1} + K'a_t` has second moments `(I − K'G)Σ(I − K'G)' + K'DD'K' − (I − K'G)CD'K' −
K'DC'(I − K'G)'` (with `C = C_{t−1}`). -/
theorem eq_10_11 (t : ℕ) (K' : Matrix X Y ℝ) :
    var_mom μ (S.err x y h u t - kf_app K' (S.innov y h u t))
        (S.err x y h u t - kf_app K' (S.innov y h u t)) =
      kf_joseph (S.G t) (S.D t) (S.Cl t) (S.Spred t) K' := by
  obtain ⟨he, -, hee, hes⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  obtain ⟨-, -, -, hff, -⟩ := kf_step (μ := μ) he (hLε t) (hLε (t + 1)) (S.G t) (S.D t)
    (S.Cl t) K' (S.A t) (S.C t) (S.kf_innov_eq hy t) rfl hee (by rw [hes t le_rfl]; simp)
    (by rw [hεε]; simp) (by rw [hes _ (Nat.le_succ t)]; simp) (by rw [hεε]; simp)
    (by rw [hεε]; simp)
  exact hff

omit [DecidableEq E] in
/-- The filtered error: `x_t − x̂_{t|t} = (x_t − x̂_{t|t−1}) − K_ta_t`. -/
theorem kf_filt_err (t : ℕ) :
    x t - S.xfilt y h u t = S.err x y h u t - kf_app (S.K t) (S.innov y h u t) := by
  rw [xfilt, err]
  abel

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- Miao, pp. 331–332: `E(x_t − x̂_{t|t})(x_t − x̂_{t|t})' = Σ_{t|t} = (I − K_tG_t)Σ_{t|t−1} −
K_tD_tC_{t−1}'`. -/
theorem kf_filt_moments (t : ℕ) :
    var_mom μ (x t - S.xfilt y h u t) (x t - S.xfilt y h u t) = S.Sfilt t := by
  have hP : (S.Spred t)ᵀ = S.Spred t := by
    obtain ⟨-, -, hee, -⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
    rw [← hee, ← kf_mom_transpose]
  rw [S.kf_filt_err, S.eq_10_11 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ]
  exact eq_10_11_gain _ _ _ hP (hΩ t)

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- **(10.10)** (Miao, p. 330), the random version: if `Ω_{t|t−1} > 0`, among all updates
`x̂_{t|t−1} + K'a_t` the Kalman gain minimises the error second-moment matrix (Loewner order) and
the mean squared error `E(x_t − x̂)'(x_t − x̂)` (its trace), uniquely. -/
theorem eq_10_10_random (t : ℕ) (hpos : (S.Om t).PosDef) (K' : Matrix X Y ℝ) :
    var_mom μ (x t - S.xfilt y h u t) (x t - S.xfilt y h u t) ≤
        var_mom μ (S.err x y h u t - kf_app K' (S.innov y h u t))
          (S.err x y h u t - kf_app K' (S.innov y h u t)) ∧
      (trace (var_mom μ (S.err x y h u t - kf_app K' (S.innov y h u t))
          (S.err x y h u t - kf_app K' (S.innov y h u t))) =
        trace (var_mom μ (x t - S.xfilt y h u t) (x t - S.xfilt y h u t)) ↔ K' = S.K t) := by
  have hP : (S.Spred t)ᵀ = S.Spred t := by
    obtain ⟨-, -, hee, -⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
    rw [← hee, ← kf_mom_transpose]
  rw [S.kf_filt_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ,
    S.eq_10_11 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ]
  obtain ⟨h1, -, h3⟩ := eq_10_10 (S.G t) (S.D t) (S.Cl t) hP hpos K'
  exact ⟨h1, h3⟩

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- Shocks dated after `s` are orthogonal to the innovation `a_s`. -/
theorem kf_shock_innov (s r : ℕ) (hr : s < r) :
    var_mom μ (ε r) (S.innov y h u s) = 0 := by
  obtain ⟨he, -, -, hes⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s
  rw [kf_mom_transpose, S.kf_innov_eq hy, kf_mom_lin2 he (hLε s) (hLε r), hes r hr.le, hεε]
  have h1 : r ≠ s := by omega
  have h2 : s ≠ r := by omega
  simp [h1, h2]

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- The projection property behind (10.12) (Miao, p. 332): the prediction error
`x_t − x̂_{t|t−1}` is orthogonal to every past innovation `a_s`, `s < t`. -/
theorem kf_err_orth (s k : ℕ) :
    var_mom μ (S.err x y h u (s + 1 + k)) (S.innov y h u s) = 0 := by
  have hM := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ
  have hI := fun t => (S.kf_innov_L2 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t).1
  have hsucc : ∀ t, var_mom μ (S.err x y h u (t + 1)) (S.innov y h u s) =
      S.A t * (var_mom μ (S.err x y h u t) (S.innov y h u s) -
        S.K t * var_mom μ (S.innov y h u t) (S.innov y h u s)) +
        S.C t * var_mom μ (ε (t + 1)) (S.innov y h u s) := by
    intro t
    rw [S.kf_err_succ hx, kf_mom_add_left (kf_L2_app (kf_L2_sub (hM t).1 (kf_L2_app (hI t) _)) _)
      (kf_L2_app (hLε _) _) (hI s), kf_mom_app_left (kf_L2_sub (hM t).1 (kf_L2_app (hI t) _))
      (hI s), kf_mom_app_left (hLε _) (hI s), kf_mom_lin_sub (hM t).1 (hI t) (hI s)]
  induction k with
  | zero =>
    rw [add_zero, hsucc, S.kf_shock_innov μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s (s + 1)
      (by omega), (S.eq_10_8 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s).1,
      (S.eq_10_8 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s).2]
    have hinv : (kf_Om (S.G s) (S.D s) (S.Cl s) (S.Spred s))⁻¹ *
        kf_Om (S.G s) (S.D s) (S.Cl s) (S.Spred s) = 1 := nonsing_inv_mul _ (hΩ s)
    simp only [K, Om, kf_gain, Matrix.mul_assoc, hinv, Matrix.mul_one, sub_self,
      Matrix.mul_zero, add_zero]
  | succ k ih =>
    rw [show s + 1 + (k + 1) = (s + 1 + k) + 1 by omega, hsucc, ih,
      S.kf_shock_innov μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s _ (by omega), S.kf_innov_eq hy,
      kf_mom_lin2 (hM _).1 (hLε _) (hI s), ih,
      S.kf_shock_innov μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s _ (by omega)]
    simp

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- Miao, p. 333: the innovations are mutually uncorrelated, `Ea_ta_s' = 0` for `s < t` (the
second-moment content of "`a_t` is independently distributed"). -/
theorem kf_innov_orth (s t : ℕ) (hst : s < t) :
    var_mom μ (S.innov y h u t) (S.innov y h u s) = 0 := by
  have hM := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  have hI := (S.kf_innov_L2 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s).1
  obtain ⟨k, rfl⟩ : ∃ k, t = s + 1 + k := ⟨t - s - 1, by omega⟩
  rw [S.kf_innov_eq hy, kf_mom_lin2 hM.1 (hLε _) hI,
    S.kf_err_orth μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ,
    S.kf_shock_innov μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s _ (by omega)]
  simp

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- The filtered error `x_t − x̂_{t|t}` is orthogonal to the innovations `a_0, …, a_t`. -/
theorem kf_filt_orth (s t : ℕ) (hst : s ≤ t) :
    var_mom μ (x t - S.xfilt y h u t) (S.innov y h u s) = 0 := by
  have hM := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  have hI := fun t => (S.kf_innov_L2 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t).1
  rw [S.kf_filt_err, kf_mom_lin_sub hM.1 (hI t) (hI s)]
  rcases eq_or_lt_of_le hst with rfl | hlt
  · rw [(S.eq_10_8 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s).1,
      (S.eq_10_8 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s).2]
    have hinv : (kf_Om (S.G s) (S.D s) (S.Cl s) (S.Spred s))⁻¹ *
        kf_Om (S.G s) (S.D s) (S.Cl s) (S.Spred s) = 1 := nonsing_inv_mul _ (hΩ s)
    simp only [K, Om, kf_gain, Matrix.mul_assoc, hinv, Matrix.mul_one, sub_self]
  · obtain ⟨k, rfl⟩ : ∃ k, t = s + 1 + k := ⟨t - s - 1, by omega⟩
    rw [S.kf_err_orth μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ,
      S.kf_innov_orth μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ s _ hlt]
    simp

/-- The innovation-based predictor term `∑_{s<n} L_sa_s`. -/
noncomputable def kf_wsum (L : ℕ → Matrix X Y ℝ) (n : ℕ) : Ω → X → ℝ :=
  ∑ s ∈ Finset.range n, kf_app (L s) (S.innov y h u s)

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- The second moments of `W_n = ∑_{s<n} L_sa_s`: square integrable, mean zero,
`E[a_rW_n'] = 0` and `E[(x_r − x̂_{r|r−1})W_n'] = 0` for `n ≤ r`, `EW_nW_n' = ∑ L_sΩ_sL_s'`. -/
theorem kf_wsum_moments (L : ℕ → Matrix X Y ℝ) (n : ℕ) :
    kf_L2 μ (S.kf_wsum (y := y) (h := h) (u := u) L n) ∧
      kf_mean μ (S.kf_wsum (y := y) (h := h) (u := u) L n) = 0 ∧
      (∀ r, n ≤ r → var_mom μ (S.innov y h u r) (S.kf_wsum (y := y) (h := h) (u := u) L n) = 0 ∧
        var_mom μ (S.err x y h u r) (S.kf_wsum (y := y) (h := h) (u := u) L n) = 0) ∧
      var_mom μ (S.kf_wsum (y := y) (h := h) (u := u) L n)
        (S.kf_wsum (y := y) (h := h) (u := u) L n) =
        ∑ s ∈ Finset.range n, L s * S.Om s * (L s)ᵀ := by
  have hI := fun t => S.kf_innov_L2 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  have hM := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ
  induction n with
  | zero =>
    simp only [kf_wsum, Finset.range_zero, Finset.sum_empty]
    refine ⟨kf_L2_zero, ?_, fun r _ => ⟨?_, ?_⟩, ?_⟩ <;>
      first | (funext i; simp [kf_mean]) | (ext i j; simp [var_mom])
  | succ n ih =>
    obtain ⟨hW, hmW, horth, hWW⟩ := ih
    have hZ := kf_L2_app (hI n).1 (L n)
    have hrec : S.kf_wsum (y := y) (h := h) (u := u) L (n + 1) =
        S.kf_wsum (y := y) (h := h) (u := u) L n + kf_app (L n) (S.innov y h u n) := by
      simp only [kf_wsum, Finset.sum_range_succ]
    rw [hrec]
    refine ⟨kf_L2_add hW hZ, ?_, fun r hr => ⟨?_, ?_⟩, ?_⟩
    · rw [kf_mean_add hW hZ, hmW, kf_mean_app (hI n).1, (hI n).2]
      simp
    · rw [kf_mom_add_right hW hZ (hI r).1, (horth r (by omega)).1, kf_mom_app_right (hI n).1
        (hI r).1, S.kf_innov_orth μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ n r (by omega)]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, r = n + 1 + k := ⟨r - n - 1, by omega⟩
      rw [kf_mom_add_right hW hZ (hM _).1, (horth _ (by omega)).2, kf_mom_app_right (hI n).1
        (hM _).1, S.kf_err_orth μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ]
      simp
    · rw [kf_mom_add_left hW hZ (kf_L2_add hW hZ), kf_mom_add_right hW hZ hW,
        kf_mom_add_right hW hZ hZ, hWW, kf_mom_app_right (hI n).1 hW,
        kf_mom_transpose (S.innov y h u n), kf_mom_app_left (hI n).1 hZ,
        kf_mom_app_right (hI n).1 (hI n).1, kf_mom_app_left (hI n).1 hW, (horth n le_rfl).1,
        (S.eq_10_8 μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ n).1, Finset.sum_range_succ]
      simp [Matrix.mul_assoc]

include hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ in
/-- **(10.12)** (Miao, p. 332), the projection theorem in second moments: `x̂_{t|t−1}` is the best
predictor of `x_t` among all predictors `x̂_{t|t−1} + ∑_{s<t}L_sa_s + c` that are affine in the
past innovations. The error second-moment matrix of such a predictor is
`Σ_{t|t−1} + ∑_{s<t}L_sΩ_{s|s−1}L_s' + cc'`, which dominates `Σ_{t|t−1}` in the Loewner order. -/
theorem eq_10_12 (t : ℕ) (L : ℕ → Matrix X Y ℝ) (c : X → ℝ) :
    var_mom μ (x t - (S.xpred y h u t + S.kf_wsum (y := y) (h := h) (u := u) L t +
        fun _ => c)) (x t - (S.xpred y h u t + S.kf_wsum (y := y) (h := h) (u := u) L t +
        fun _ => c)) =
      S.Spred t + ∑ s ∈ Finset.range t, L s * S.Om s * (L s)ᵀ + Matrix.of (fun i j => c i * c j) ∧
      S.Spred t ≤ var_mom μ (x t - (S.xpred y h u t + S.kf_wsum (y := y) (h := h) (u := u) L t +
        fun _ => c)) (x t - (S.xpred y h u t + S.kf_wsum (y := y) (h := h) (u := u) L t +
        fun _ => c)) := by
  obtain ⟨he, hme, hee, -⟩ := S.kf_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ t
  obtain ⟨hW, hmW, horth, hWW⟩ :=
    S.kf_wsum_moments μ hx hy hL0 hLε hm0 hmε hS0 hεε h0ε hΩ L t
  set W := S.kf_wsum (y := y) (h := h) (u := u) L t
  have hc := kf_L2_const (μ := μ) c
  have hrw : x t - (S.xpred y h u t + W + fun _ => c) = (S.err x y h u t - W) - fun _ => c := by
    rw [err]
    abel
  have hd := kf_L2_sub he hW
  have hmd : kf_mean μ (S.err x y h u t - W) = 0 := by
    rw [kf_mean_sub he hW, hme, hmW, sub_zero]
  have hdd : var_mom μ (S.err x y h u t - W) (S.err x y h u t - W) =
      S.Spred t + var_mom μ W W := by
    rw [kf_mom_sub_left he hW hd, kf_mom_sub_right he hW he, kf_mom_sub_right he hW hW, hee,
      (horth t le_rfl).2, kf_mom_transpose (S.err x y h u t) W, (horth t le_rfl).2]
    simp
  have hcc : var_mom μ (fun _ : Ω => c) (fun _ : Ω => c) = Matrix.of (fun i j => c i * c j) := by
    rw [kf_mom_const_left, kf_mean_const]
  have hdc : var_mom μ (S.err x y h u t - W) (fun _ : Ω => c) = 0 := by
    rw [kf_mom_const_right, hmd]
    ext i j
    simp
  have hcd : var_mom μ (fun _ : Ω => c) (S.err x y h u t - W) = 0 := by
    rw [kf_mom_transpose, hdc, transpose_zero]
  have htot : var_mom μ (x t - (S.xpred y h u t + W + fun _ => c))
      (x t - (S.xpred y h u t + W + fun _ => c)) =
      S.Spred t + ∑ s ∈ Finset.range t, L s * S.Om s * (L s)ᵀ +
        Matrix.of (fun i j => c i * c j) := by
    rw [hrw, kf_mom_sub_left hd hc (kf_L2_sub hd hc), kf_mom_sub_right hd hc hd,
      kf_mom_sub_right hd hc hc, hdd, hdc, hcd, hcc, hWW]
    abel
  refine ⟨htot, ?_⟩
  rw [htot, Matrix.le_iff, add_assoc, add_sub_cancel_left, ← hWW, ← hcc]
  exact (kf_mom_self_psd hW).add (kf_mom_self_psd hc)

/-! ### Recursive forms (Miao, p. 333) -/

omit [DecidableEq E] in
/-- Miao, p. 333: the fully recursive form `x̂_{t+1|t} = A_tx̂_{t|t−1} + B_tu_t + A_tK_ta_t`. -/
theorem kf_pred_recursive (t : ℕ) :
    S.xpred y h u (t + 1) = kf_app (S.A t) (S.xpred y h u t) + kf_app (S.B t) (u t) +
      kf_app (S.A t * S.K t) (S.innov y h u t) := by
  rw [xpred_succ, xfilt, kf_app_add, kf_app_app]
  abel

omit [DecidableEq E] in
/-- Miao, p. 333: the alternative form `x̂_{t+1|t+1} = A_tx̂_{t|t} + B_tu_t + K_{t+1}a_{t+1}`. -/
theorem kf_filt_recursive (t : ℕ) :
    S.xfilt y h u (t + 1) = kf_app (S.A t) (S.xfilt y h u t) + kf_app (S.B t) (u t) +
      kf_app (S.K (t + 1)) (S.innov y h u (t + 1)) := by
  rw [xfilt, xpred_succ]

omit [Fintype U] [DecidableEq E] in
/-- Miao, p. 333: the Riccati equation for the predicted covariances,
`Σ_{t+1|t} = A_tΣ_{t|t−1}A_t' + C_tC_t' − A_t(G_tΣ_{t|t−1} + D_tC'_{t−1})'Ω⁻¹(G_tΣ_{t|t−1} +
D_tC'_{t−1})A_t'`, for symmetric `Σ_{t|t−1}` and invertible `Ω_{t|t−1}`. -/
theorem kf_riccati_Spred (t : ℕ) (hP : (S.Spred t)ᵀ = S.Spred t) (hu : IsUnit (S.Om t).det) :
    S.Spred (t + 1) = S.A t * S.Spred t * (S.A t)ᵀ + S.C t * (S.C t)ᵀ -
      S.A t * (S.G t * S.Spred t + S.D t * (S.Cl t)ᵀ)ᵀ * (S.Om t)⁻¹ *
        (S.G t * S.Spred t + S.D t * (S.Cl t)ᵀ) * (S.A t)ᵀ :=
  kf_riccati_pred _ _ _ _ _ hP hu

omit [Fintype U] [DecidableEq E] in
/-- Miao, p. 333: the recursion for the filtered covariances,
`Σ_{t+1|t+1} = (I − K_{t+1}G_{t+1})(A_tΣ_{t|t}A_t' + C_tC_t') − K_{t+1}D_{t+1}C_t'`. -/
theorem kf_riccati_Sfilt (t : ℕ) :
    S.Sfilt (t + 1) = (1 - S.K (t + 1) * S.G (t + 1)) *
      (S.A t * S.Sfilt t * (S.A t)ᵀ + S.C t * (S.C t)ᵀ) -
      S.K (t + 1) * S.D (t + 1) * (S.C t)ᵀ := rfl

end KFSystem

/-! ### The printed cross covariance (10.9) -/

/-- The uniform probability on two points. -/
noncomputable def kf_twoPoint : Measure (Fin 2) := (2 : ENNReal)⁻¹ • Measure.count

/-- The two-point measure is a probability measure. -/
theorem kf_twoPoint_prob : IsProbabilityMeasure kf_twoPoint := by
  constructor
  simp only [kf_twoPoint, Measure.smul_apply, Measure.count_univ, smul_eq_mul,
    ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  simp only [Nat.cast_ofNat]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- Integrals against the two-point measure. -/
theorem kf_twoPoint_integral (f : Fin 2 → ℝ) : ∫ ω, f ω ∂kf_twoPoint = (f 0 + f 1) / 2 := by
  have := kf_twoPoint_prob
  rw [integral_fintype]
  · simp [kf_twoPoint, Fin.sum_univ_two, Measure.real]
    ring
  · exact Integrable.of_finite

/-- (10.9) as printed is false at `t = 0` (Miao, p. 330): the book's
`E[(x_t − x̂_{t|t−1})ε_t'] = C_t` fails for `t = 0`, where the cross moment is `Cℓ₀ = 0`. Here
`x₀ = x̄₀ = 0`, `Σ₀ = 0`, `C₀ = 1`, and `ε₀ = ±1` with probability `½` each (mean `0`, variance
`1`, uncorrelated with `x₀`). -/
theorem kf_cross_book_false :
    ∃ (S : KFSystem (Fin 1) (Fin 1) (Fin 1) (Fin 1)) (x : ℕ → Fin 2 → Fin 1 → ℝ)
      (ε : ℕ → Fin 2 → Fin 1 → ℝ),
      kf_mean kf_twoPoint (ε 0) = 0 ∧ var_mom kf_twoPoint (ε 0) (ε 0) = 1 ∧
      var_mom kf_twoPoint (x 0 - fun _ => S.xbar0) (x 0 - fun _ => S.xbar0) = S.S0 ∧
      var_mom kf_twoPoint (x 0 - fun _ => S.xbar0) (ε 0) = 0 ∧
      ∀ (y h : ℕ → Fin 2 → Fin 1 → ℝ) (u : ℕ → Fin 2 → Fin 1 → ℝ),
        var_mom kf_twoPoint (S.err x y h u 0) (ε 0) = S.Cl 0 ∧
        var_mom kf_twoPoint (S.err x y h u 0) (ε 0) ≠ S.C 0 := by
  refine ⟨⟨fun _ => 1, fun _ => 0, fun _ => 1, fun _ => 1, fun _ => 0, fun _ => 0, 0, 0⟩,
    fun _ _ => 0, fun _ ω _ => if ω = 0 then 1 else -1, ?_, ?_, ?_, ?_, fun y h u => ⟨?_, ?_⟩⟩
  · funext i
    simp [kf_mean, kf_twoPoint_integral]
  · ext i j
    fin_cases i
    fin_cases j
    simp [var_mom, kf_twoPoint_integral]
  · ext i j
    simp [var_mom]
  · ext i j
    simp [var_mom]
  · ext i j
    simp [var_mom, KFSystem.err, KFSystem.xpred, KFSystem.Cl]
  · intro h0
    have := congrFun (congrFun h0 0) 0
    simp [var_mom, KFSystem.err, KFSystem.xpred] at this
end Miao.PartialInformation
