/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoclassicalGrowth.RXTree
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# §14.3.3 Capital adjustment costs: the planner and the three decentralisations

Miao, §14.3.3, pp. 494–500, and Exercise 14.5, p. 508. Capital accumulates as
`K_{t+1} = (1 − δ)Kₜ + Φ(Iₜ, Kₜ)` (14.42), with `Φ_I > 0`, `Φ_II < 0`, often
`Φ(I, K) = ϕ(I/K)K` (14.43) with `ϕ″ < 0`, `ϕ(δ) = δ`, `ϕ′(δ) = 1`, `ϕ″(δ) = κ`.

* (14.43): linear homogeneity, partial derivatives `Φ_I = ϕ′(I/K)`,
  `Φ_K = ϕ(I/K) − (I/K)ϕ′(I/K)`, `Φ_II = ϕ″(I/K)/K < 0` (`rx_Phi`, `rx_Phi_homog`,
  `rx_Phi_partials`, `rx_Phi_II`); the steady state `I/K = δ`, `Q = 1`, `Φ_K = 0`
  (`rx_Phi_steady`, `eq_14_43_steady`), and the normalisation forces `κ < 0` (`rx_kappa_neg`).
  The concrete `ϕ(i) = i + κ(i − δ)²/2` (`rx_phiQuad`) satisfies all the normalisations
  (`rx_phiQuad_normalised`).
* The first-order conditions are derived by perturbing `K_{t+1}` at a node, the investment
  changes being given by the inverse `G(·, K)` of `Φ(·, K)` (`rx_inverse_partials`): the
  generic node Euler equation `rx_uzawa_euler`, with `Q = 1/Φ_I` (the `Iₜ` condition
  `QΦ_I = 1`, also the stationarity of the Lagrangian in `Iₜ`, `rx_invest_foc`).
* The planner (14.44)–(14.45): `eq_14_45_N` (labour), `eq_14_45_K` (capital).
* Decentralisation 1 (households own capital), (14.46)–(14.47): the household's labour and
  capital conditions (`rx_dec1_labour`, `rx_dec1_euler`), the firm's
  `R_k = zF_K`, `w = zF_N` (`eq_14_47_foc`).
* Decentralisation 2 (stock market): the household's share and bond conditions
  (`rx_dec2_shares`, `rx_dec2_bonds`), the firm's (14.48)–(14.49) (`eq_14_48`, `eq_14_49`).
* Decentralisation 3 (capital goods producers): the producer's `QΦ_I = 1`
  (`rx_dec3_producer`) and the household's Euler equation (`rx_dec3_euler`).
* **Exercise 14.5**: decentralisations 1 and 2 have the planner's equilibrium conditions
  (`ex_14_5_dec1`, `ex_14_5_dec2`, budgets ⇒ resource constraint `ex_14_5_budgets`).
  **Correction**: decentralisation 3 as printed does not: the household does not internalise
  `Φ_K`, so its Euler equation lacks the term `Q_{t+1}Φ_K` (`ex_14_5_dec3_iff`); the two
  Euler equations are incompatible whenever `Φ_K` has a strict sign at all successors
  (`ex_14_5_dec3_counterexample`), which happens for (14.43) off the steady state
  (`rx_Phi_K_pos`, `rx_phiQuad_K`). They agree when `Φ_K ≡ 0` and when the household's capital
  also earns the producers' rent `QΦ_KK` (`ex_14_5_dec3_corrected`).
* "In the case without capital adjustment costs (`Φ = I`), `Qₜ = 1`" (`rx_no_adjustment_Q`).
-/

namespace Miao.NeoclassicalGrowth

open Filter Topology

/-- The adjustment cost function (14.43), `Φ(I, K) = ϕ(I/K)K` (Miao, p. 495). -/
noncomputable def rx_Phi (ϕ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := ϕ (p.1 / p.2) * p.2

/-- Miao, p. 495: (14.43) is linearly homogeneous. -/
theorem rx_Phi_homog (ϕ : ℝ → ℝ) {l : ℝ} (hl : l ≠ 0) (I K : ℝ) :
    rx_Phi ϕ (l * I, l * K) = l * rx_Phi ϕ (I, K) := by
  simp only [rx_Phi]
  rw [mul_div_mul_left I K hl]
  ring

/-- Miao, p. 495: the partial derivatives of (14.43), `Φ_I = ϕ′(I/K)` and
`Φ_K = ϕ(I/K) − (I/K)ϕ′(I/K)`, at `K > 0`. -/
theorem rx_Phi_partials {ϕ : ℝ → ℝ} {d : ℝ} {I K : ℝ} (hK : K ≠ 0)
    (hϕ : HasDerivAt ϕ d (I / K)) : rx_HasPartials (rx_Phi ϕ) d (ϕ (I / K) - I / K * d) (I, K) := by
  have hinv : HasFDerivAt (fun p : ℝ × ℝ => p.2⁻¹)
      (-((K ^ 2)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) (I, K) := by
    have h0 : HasDerivAt (fun x : ℝ => x⁻¹) (-(K ^ 2)⁻¹) ((I, K).2) := hasDerivAt_inv hK
    have := h0.comp_hasFDerivAt (𝕜 := ℝ) (f := Prod.snd) (I, K)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (I, K)))
    simpa [Function.comp_def] using this
  have hdiv : HasFDerivAt (fun p : ℝ × ℝ => p.1 * p.2⁻¹)
      (I • (-((K ^ 2)⁻¹ • ContinuousLinearMap.snd ℝ ℝ ℝ)) +
        K⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ) (I, K) :=
    (hasFDerivAt_fst (p := (I, K))).mul hinv
  have hϕ' : HasDerivAt ϕ d ((fun p : ℝ × ℝ => p.1 * p.2⁻¹) (I, K)) := by
    simpa [div_eq_mul_inv] using hϕ
  have hcomp := hϕ'.comp_hasFDerivAt (I, K) hdiv
  have hfull := hcomp.mul (hasFDerivAt_snd (p := (I, K)))
  unfold rx_HasPartials
  have heq : rx_Phi ϕ = (fun p : ℝ × ℝ => (ϕ ∘ fun p : ℝ × ℝ => p.1 * p.2⁻¹) p * p.2) := by
    funext p
    simp [rx_Phi, div_eq_mul_inv]
  rw [heq]
  refine hfull.congr_fderiv ?_
  ext
  · simp [div_eq_mul_inv]
    field_simp
  · simp [div_eq_mul_inv]
    field_simp
    ring

/-- The partial derivative in the first argument, as a one-variable derivative. -/
theorem rx_HasPartials.fst {Ψ : ℝ × ℝ → ℝ} {a b I K : ℝ} (h : rx_HasPartials Ψ a b (I, K)) :
    HasDerivAt (fun x => Ψ (x, K)) a I := by
  have := h.comp (x := fun x => x) (y := fun _ => K) (k := I) (hasDerivAt_id I)
    (hasDerivAt_const I K)
  simpa using this

/-- The partial derivative in the second argument, as a one-variable derivative. -/
theorem rx_HasPartials.snd {Ψ : ℝ × ℝ → ℝ} {a b I K : ℝ} (h : rx_HasPartials Ψ a b (I, K)) :
    HasDerivAt (fun y => Ψ (I, y)) b K := by
  have := h.comp (x := fun _ => I) (y := fun y => y) (k := K) (hasDerivAt_const K I)
    (hasDerivAt_id K)
  simpa using this

/-- Miao, p. 495: `Φ_II = ϕ″(I/K)/K`, negative when `ϕ″ < 0` and `K > 0` (the book's
`Φ_II < 0`). -/
theorem rx_Phi_II {dϕ : ℝ → ℝ} {d2 I K : ℝ} (hd2 : HasDerivAt dϕ d2 (I / K)) :
    HasDerivAt (fun x => dϕ (x / K)) (d2 / K) I ∧ (d2 < 0 → 0 < K → d2 / K < 0) := by
  have := hd2.comp I ((hasDerivAt_id' I).div_const K)
  exact ⟨this.congr_deriv (by ring), fun h1 h2 => div_neg_of_neg_of_pos h1 h2⟩

/-- Miao, p. 495: at `I = δK` the normalisations `ϕ(δ) = δ`, `ϕ′(δ) = 1` give `Φ = δK`,
`Φ_I = 1` and `Φ_K = 0`. -/
theorem rx_Phi_steady {ϕ dϕ : ℝ → ℝ} {δ K : ℝ} (hK : K ≠ 0) (h0 : ϕ δ = δ) (h1 : dϕ δ = 1) :
    rx_Phi ϕ (δ * K, K) = δ * K ∧ dϕ (δ * K / K) = 1 ∧
      ϕ (δ * K / K) - δ * K / K * dϕ (δ * K / K) = 0 := by
  have e : δ * K / K = δ := by field_simp
  simp [rx_Phi, e, h0, h1]

/-- Miao, p. 495, (14.43): "this assumption ensures that the investment rate is `I/K = δ` and
`Q = 1` in the nonstochastic steady state". If `ϕ` is strictly increasing (`Φ_I > 0`),
`ϕ(δ) = δ`, `ϕ′(δ) = 1`, and a steady state satisfies `K = (1 − δ)K + Φ(I, K)` with `K > 0`,
`QΦ_I = 1` and the Euler equation `1 = β(zF_K + Q(1 − δ + Φ_K))`, then `I/K = δ`, `Q = 1` and
`zF_K = 1/β − 1 + δ`: the steady state is that of the model without adjustment costs, whatever
`κ = ϕ″(δ)`. -/
theorem eq_14_43_steady {ϕ dϕ : ℝ → ℝ} {δ β K I Q zFK : ℝ} (hβ : 0 < β) (hK : 0 < K)
    (hmono : StrictMono ϕ) (h0 : ϕ δ = δ) (h1 : dϕ δ = 1)
    (hacc : K = (1 - δ) * K + rx_Phi ϕ (I, K)) (hQ : Q * dϕ (I / K) = 1)
    (heuler : 1 = β * (zFK + Q * (1 - δ + (ϕ (I / K) - I / K * dϕ (I / K))))) :
    I / K = δ ∧ Q = 1 ∧ zFK = 1 / β - 1 + δ := by
  have hϕ : ϕ (I / K) = δ := by
    simp only [rx_Phi] at hacc
    have : (ϕ (I / K) - δ) * K = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hK.ne'
  have hi : I / K = δ := hmono.injective (hϕ.trans h0.symm)
  rw [hi, h1, mul_one] at hQ
  refine ⟨hi, hQ, ?_⟩
  rw [hi, h0, h1, hQ] at heuler
  field_simp
  linarith

/-- Miao, p. 495: with `ϕ″ < 0` everywhere, the parameter `κ = ϕ″(δ)` is negative. -/
theorem rx_kappa_neg {d2 : ℝ → ℝ} {δ κ : ℝ} (h : ∀ i, d2 i < 0) (hκ : d2 δ = κ) : κ < 0 :=
  hκ ▸ h δ

/-- A concrete adjustment function for (14.43): `ϕ(i) = i + κ(i − δ)²/2`. -/
noncomputable def rx_phiQuad (δ κ i : ℝ) : ℝ := i + κ * (i - δ) ^ 2 / 2

/-- `rx_phiQuad` satisfies the normalisations of (14.43): `ϕ(δ) = δ`, `ϕ′(i) = 1 + κ(i − δ)`
(so `ϕ′(δ) = 1`) and `ϕ″ = κ` (so `ϕ″ < 0` for `κ < 0`). -/
theorem rx_phiQuad_normalised (δ κ : ℝ) :
    rx_phiQuad δ κ δ = δ ∧ (∀ i, HasDerivAt (rx_phiQuad δ κ) (1 + κ * (i - δ)) i) ∧
      (1 + κ * (δ - δ) = 1) ∧ (∀ i, HasDerivAt (fun j => 1 + κ * (j - δ)) κ i) := by
  refine ⟨by simp [rx_phiQuad], fun i => ?_, by ring, fun i => ?_⟩
  · have h0 := (hasDerivAt_id' i).sub_const δ
    have h := ((h0.mul h0).const_mul κ).div_const 2
    have := (hasDerivAt_id' i).add h
    unfold rx_phiQuad
    simp only [sq]
    exact this.congr_deriv (by ring)
  · have := (((hasDerivAt_id i).sub_const δ).const_mul κ).const_add 1
    simpa using this

/-- For `rx_phiQuad`, `Φ_K = ϕ(i) − iϕ′(i) = −κ(i² − δ²)/2`, positive when `κ < 0` and
`0 ≤ δ < i` (investment above its steady-state rate). -/
theorem rx_phiQuad_K (δ κ i : ℝ) :
    rx_phiQuad δ κ i - i * (1 + κ * (i - δ)) = -κ * (i ^ 2 - δ ^ 2) / 2 ∧
      (κ < 0 → 0 ≤ δ → δ < i → 0 < -κ * (i ^ 2 - δ ^ 2) / 2) := by
  refine ⟨by unfold rx_phiQuad; ring, fun hκ hδ hi => ?_⟩
  have : 0 < i ^ 2 - δ ^ 2 := by nlinarith
  have : 0 < -κ * (i ^ 2 - δ ^ 2) := mul_pos (by linarith) this
  linarith

/-- Miao, p. 495, (14.43): `Φ_K = ϕ(i) − iϕ′(i)` is strictly positive for `i > δ > 0` when
`ϕ″ < 0`, `ϕ(δ) = δ`, `ϕ′(δ) = 1`: its derivative is `−iϕ″(i) > 0` and it vanishes at
`i = δ`. -/
theorem rx_Phi_K_pos {ϕ dϕ d2 : ℝ → ℝ} {δ i : ℝ} (hϕ : ∀ x, HasDerivAt ϕ (dϕ x) x)
    (hdϕ : ∀ x, HasDerivAt dϕ (d2 x) x) (hneg : ∀ x, d2 x < 0) (h0 : ϕ δ = δ) (h1 : dϕ δ = 1)
    (hδ : 0 < δ) (hi : δ < i) : 0 < ϕ i - i * dϕ i := by
  have hg : ∀ x, HasDerivAt (fun y => ϕ y - y * dϕ y) (-(x * d2 x)) x := by
    intro x
    have := (hϕ x).sub ((hasDerivAt_id' x).mul (hdϕ x))
    exact this.congr_deriv (by ring)
  have hmono : StrictMonoOn (fun y => ϕ y - y * dϕ y) (Set.Ioi 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
      (fun x _ => (hg x).continuousAt.continuousWithinAt) (fun x hx => ?_)
    rw [interior_Ioi] at hx
    rw [(hg x).deriv]
    have : 0 < x := hx
    nlinarith [hneg x]
  have := hmono (show δ ∈ Set.Ioi 0 from hδ) (show i ∈ Set.Ioi 0 from hδ.trans hi) hi
  simp only [h0, h1, mul_one, sub_self] at this
  exact this

/-- The partial derivatives of the inverse `G(·, K)` of `Φ(·, K)`: differentiating
`Φ(G(X, K), K) = X` gives `Φ_I G_X = 1` and `Φ_I G_K + Φ_K = 0`. -/
theorem rx_inverse_partials {Φ G : ℝ × ℝ → ℝ} (hΦG : ∀ X K, Φ (G (X, K), K) = X)
    {X K gX gK a b : ℝ} (hG : rx_HasPartials G gX gK (X, K))
    (hΦ : rx_HasPartials Φ a b (G (X, K), K)) : a * gX = 1 ∧ a * gK + b = 0 := by
  constructor
  · have hp : HasDerivAt (fun x => G (x, K)) gX X := hG.fst
    have d := hΦ.comp (x := fun x => G (x, K)) (y := fun _ => K) (k := X) hp
      (hasDerivAt_const X K)
    have d' : HasDerivAt (fun x => Φ (G (x, K), K)) 1 X := by
      simpa [hΦG] using hasDerivAt_id' X
    have := d.unique d'
    linarith
  · have hp : HasDerivAt (fun y => G (X, y)) gK K := hG.snd
    have d := hΦ.comp (x := fun y => G (X, y)) (y := fun y => y) (k := K) hp (hasDerivAt_id K)
    have d' : HasDerivAt (fun y => Φ (G (X, y), y)) 0 K := by
      simpa [hΦG] using hasDerivAt_const K X
    have := d.unique d'
    linarith

/-- The node Euler equation with adjustment costs in the accumulation equation (14.42).
At the node `h`, `K_{t+1} = k` is financed by `Iₜ = G(k − (1 − δ)Kₜ, Kₜ)` out of income `y₀`,
and at each successor `s` the investment `I_{t+1}(s) = G(K_{t+2}(s) − (1 − δ)k, k)` keeps
`K_{t+2}(s)` fixed, out of income `y₁ₛ(k)` with `y₁ₛ′(K_{t+1}) = r₁ₛ`. With `QₜΦ_I(Iₜ, Kₜ) = 1`,
`Q_{t+1}Φ_I(I_{t+1}, K_{t+1}) = 1` and `Φ_K(I_{t+1}, K_{t+1}) = b₁`, a local maximum of
`U₀(cₜ) + βEₜU₁(c_{t+1})` gives `ΛₜQₜ = βEₜ[Λ_{t+1}(r_{t+1} + Q_{t+1}(1 − δ + Φ_K))]`. -/
theorem rx_uzawa_euler {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {Φ G : ℝ × ℝ → ℝ} (hΦG : ∀ X K, Φ (G (X, K), K) = X)
    {δ β Kt K1 y0 l0 a0 b0 gX0 gK0 Q0 : ℝ} {K2 l1 r1 a1 b1 gX1 gK1 Q1 : S → ℝ}
    {U0 : ℝ → ℝ} {U1 y1 : S → ℝ → ℝ}
    (hG0 : rx_HasPartials G gX0 gK0 (K1 - (1 - δ) * Kt, Kt))
    (hΦ0 : rx_HasPartials Φ a0 b0 (G (K1 - (1 - δ) * Kt, Kt), Kt))
    (hG1 : ∀ s, rx_HasPartials G (gX1 s) (gK1 s) (K2 s - (1 - δ) * K1, K1))
    (hΦ1 : ∀ s, rx_HasPartials Φ (a1 s) (b1 s) (G (K2 s - (1 - δ) * K1, K1), K1))
    (hQ0 : Q0 * a0 = 1) (hQ1 : ∀ s, Q1 s * a1 s = 1)
    (hy1 : ∀ s, HasDerivAt (y1 s) (r1 s) K1)
    (hU0 : HasDerivAt U0 l0 (y0 - G (K1 - (1 - δ) * Kt, Kt)))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (y1 s K1 - G (K2 s - (1 - δ) * K1, K1)))
    (hmax : IsLocalMax (fun k => U0 (y0 - G (k - (1 - δ) * Kt, Kt)) + β * ∑ s,
      T.cp h s * U1 s (y1 s k - G (K2 s - (1 - δ) * k, k))) K1) :
    l0 * Q0 = β * rx_Es T h (fun s => l1 s * (r1 s + Q1 s * (1 - δ + b1 s))) := by
  obtain ⟨e0, -⟩ := rx_inverse_partials hΦG hG0 hΦ0
  have hgX0 : gX0 = Q0 := by
    calc gX0 = gX0 * (Q0 * a0) := by rw [hQ0, mul_one]
      _ = Q0 * (a0 * gX0) := by ring
      _ = Q0 := by rw [e0, mul_one]
  have hgX1 : ∀ s, gX1 s = Q1 s ∧ gK1 s = -(Q1 s * b1 s) := by
    intro s
    obtain ⟨e1, e2⟩ := rx_inverse_partials hΦG (hG1 s) (hΦ1 s)
    have hq := hQ1 s
    constructor
    · calc gX1 s = gX1 s * (Q1 s * a1 s) := by rw [hq, mul_one]
        _ = Q1 s * (a1 s * gX1 s) := by ring
        _ = Q1 s := by rw [e1, mul_one]
    · calc gK1 s = gK1 s * (Q1 s * a1 s) := by rw [hq, mul_one]
        _ = Q1 s * (a1 s * gK1 s + b1 s) - Q1 s * b1 s := by ring
        _ = -(Q1 s * b1 s) := by rw [e2]; ring
  have hc0 : HasDerivAt (fun k => y0 - G (k - (1 - δ) * Kt, Kt)) (0 - (gX0 * 1 + gK0 * 0)) K1 :=
    (hasDerivAt_const K1 y0).sub (hG0.comp (x := fun k => k - (1 - δ) * Kt) (y := fun _ => Kt)
      ((hasDerivAt_id K1).sub_const _) (hasDerivAt_const K1 Kt))
  have hc1 : ∀ s, HasDerivAt (fun k => y1 s k - G (K2 s - (1 - δ) * k, k))
      (r1 s - (gX1 s * (0 - (1 - δ) * 1) + gK1 s * 1)) K1 := fun s =>
    (hy1 s).sub ((hG1 s).comp (x := fun k => K2 s - (1 - δ) * k) (y := fun k => k)
      ((hasDerivAt_const K1 _).sub ((hasDerivAt_id K1).const_mul _)) (hasDerivAt_id K1))
  have e := rx_node_foc (c0 := fun k => y0 - G (k - (1 - δ) * Kt, Kt))
    (c1 := fun s k => y1 s k - G (K2 s - (1 - δ) * k, k)) hU0 hc0 hU1 hc1 hmax
  have hs : ∀ s, T.cp h s * (l1 s * (r1 s - (gX1 s * (0 - (1 - δ) * 1) + gK1 s * 1))) =
      T.cp h s * (l1 s * (r1 s + Q1 s * (1 - δ + b1 s))) := by
    intro s
    rw [(hgX1 s).1, (hgX1 s).2]
    ring
  rw [Finset.sum_congr rfl fun s _ => hs s, hgX0] at e
  simp only [rx_Es]
  linarith

/-- Miao, (14.45), p. 496, and (14.48), p. 498: the `Iₜ` condition `QₜΦ_I(Iₜ, Kₜ) = 1`. The
terms of the Lagrangian in `Iₜ` are `Λ(−Iₜ) + ΛQΦ(Iₜ, Kₜ)` (multiplier `Λ` on the resource or
dividend constraint, `ΛQ` on (14.42)); their derivative is `Λ(QΦ_I − 1)`, which vanishes iff
`QΦ_I = 1` when `Λ ≠ 0`. -/
theorem rx_invest_foc {Φ : ℝ × ℝ → ℝ} {Λ Q I K a : ℝ} (hΦ : HasDerivAt (fun x => Φ (x, K)) a I) :
    HasDerivAt (fun x => Λ * -x + Λ * Q * Φ (x, K)) (Λ * (Q * a - 1)) I ∧
      (Λ ≠ 0 → (Λ * (Q * a - 1) = 0 ↔ Q * a = 1)) := by
  refine ⟨?_, fun hΛ => ?_⟩
  · have := ((hasDerivAt_id' I).neg.const_mul Λ).add (hΦ.const_mul (Λ * Q))
    exact this.congr_deriv (by ring)
  · constructor
    · intro h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hΛ
      · linarith
    · intro h0
      rw [h0, sub_self, mul_zero]

/-- Miao, p. 498: "In the case without capital adjustment costs (i.e., `Φ(I, K) = I`),
`Qₜ = 1`". -/
theorem rx_no_adjustment_Q {Q I K : ℝ} {a : ℝ} (hΦ : HasDerivAt (fun x => (fun p : ℝ × ℝ => p.1)
    (x, K)) a I) (hQ : Q * a = 1) : Q = 1 := by
  have : a = 1 := hΦ.unique (hasDerivAt_id' I)
  rw [this, mul_one] at hQ
  exact hQ

/-- A labour first-order condition: if `n ↦ U(c(n), n)` has a local maximum at `N`, with
`c′(N) = c_N`, `U_C = Λ`, `U_N = u_N`, then `Λc_N + u_N = 0`. -/
theorem rx_labour_foc {U : ℝ × ℝ → ℝ} {c : ℝ → ℝ} {N cn l uN : ℝ}
    (hU : rx_HasPartials U l uN (c N, N)) (hc : HasDerivAt c cn N)
    (hmax : IsLocalMax (fun n => U (c n, n)) N) : l * cn + uN = 0 := by
  have := hU.comp (x := c) (y := fun n => n) (k := N) hc (hasDerivAt_id N)
  have e := hmax.hasDerivAt_eq_zero this
  linarith

/-- Miao, (14.45), p. 496, the planner's `Nₜ` condition `−u_N(Cₜ, Nₜ) = ΛₜzₜF_N(Kₜ, Nₜ)`
with `Λₜ = u_C(Cₜ, Nₜ)`, from perturbing `Nₜ` in `Cₜ = zₜF(Kₜ, Nₜ) − Iₜ`. -/
theorem eq_14_45_N {U F : ℝ × ℝ → ℝ} {z K I N FN l uN : ℝ}
    (hU : rx_HasPartials U l uN (z * F (K, N) - I, N)) (hF : HasDerivAt (fun n => F (K, n)) FN N)
    (hmax : IsLocalMax (fun n => U (z * F (K, n) - I, n)) N) : -uN = l * (z * FN) := by
  have hc : HasDerivAt (fun n => z * F (K, n) - I) (z * FN - 0) N :=
    (hF.const_mul z).sub (hasDerivAt_const N I)
  have := rx_labour_foc (c := fun n => z * F (K, n) - I) hU hc hmax
  linarith

/-- Miao, (14.45), p. 496, the planner's `K_{t+1}` condition
`ΛₜQₜ = βEₜΛ_{t+1}(z_{t+1}F_K(K_{t+1}, N_{t+1}) + Q_{t+1}(1 − δ + Φ_K(I_{t+1}, K_{t+1})))`,
from perturbing `K_{t+1}` in the resource constraint (14.44)
`Cₜ = zₜF(Kₜ, Nₜ) − Iₜ` with (14.42), `Λ = u_C`, `QΦ_I = 1`. -/
theorem eq_14_45_K {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {Φ G F : ℝ × ℝ → ℝ} (hΦG : ∀ X K, Φ (G (X, K), K) = X)
    {δ β Kt K1 zt Nt l0 a0 b0 gX0 gK0 Q0 : ℝ} {z N FK K2 l1 a1 b1 gX1 gK1 Q1 : S → ℝ}
    {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hG0 : rx_HasPartials G gX0 gK0 (K1 - (1 - δ) * Kt, Kt))
    (hΦ0 : rx_HasPartials Φ a0 b0 (G (K1 - (1 - δ) * Kt, Kt), Kt))
    (hG1 : ∀ s, rx_HasPartials G (gX1 s) (gK1 s) (K2 s - (1 - δ) * K1, K1))
    (hΦ1 : ∀ s, rx_HasPartials Φ (a1 s) (b1 s) (G (K2 s - (1 - δ) * K1, K1), K1))
    (hQ0 : Q0 * a0 = 1) (hQ1 : ∀ s, Q1 s * a1 s = 1)
    (hF : ∀ s, HasDerivAt (fun k => F (k, N s)) (FK s) K1)
    (hU0 : HasDerivAt U0 l0 (zt * F (Kt, Nt) - G (K1 - (1 - δ) * Kt, Kt)))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (z s * F (K1, N s) - G (K2 s - (1 - δ) * K1, K1)))
    (hmax : IsLocalMax (fun k => U0 (zt * F (Kt, Nt) - G (k - (1 - δ) * Kt, Kt)) + β * ∑ s,
      T.cp h s * U1 s (z s * F (k, N s) - G (K2 s - (1 - δ) * k, k))) K1) :
    l0 * Q0 = β * rx_Es T h (fun s => l1 s * (z s * FK s + Q1 s * (1 - δ + b1 s))) :=
  rx_uzawa_euler T h hΦG (y1 := fun s k => z s * F (k, N s)) hG0 hΦ0 hG1 hΦ1 hQ0 hQ1
    (fun s => (hF s).const_mul (z s)) hU0 hU1 hmax

/-- Miao, p. 496, decentralisation 1: the household's `Nₜ` condition `−u_N = Λₜwₜ`, from
perturbing `Nₜ` in the budget (14.46) `Cₜ = R_{kt}Kₜ + wₜNₜ − Iₜ`. -/
theorem rx_dec1_labour {U : ℝ × ℝ → ℝ} {y w N l uN : ℝ}
    (hU : rx_HasPartials U l uN (y + w * N, N)) (hmax : IsLocalMax (fun n => U (y + w * n, n)) N) :
    -uN = l * w := by
  have hc : HasDerivAt (fun n => y + w * n) (w * 1) N :=
    ((hasDerivAt_id N).const_mul w).const_add y
  have := rx_labour_foc (c := fun n => y + w * n) hU hc hmax
  linarith

/-- Miao, p. 496, decentralisation 1: the household's `K_{t+1}` condition
`ΛₜQₜ = βEₜΛ_{t+1}[R_{k,t+1} + Q_{t+1}(1 − δ + Φ_K(I_{t+1}, K_{t+1}))]`, from perturbing
`K_{t+1}` in (14.46) with (14.42). -/
theorem rx_dec1_euler {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {Φ G : ℝ × ℝ → ℝ} (hΦG : ∀ X K, Φ (G (X, K), K) = X)
    {δ β Kt K1 yt l0 a0 b0 gX0 gK0 Q0 : ℝ} {R wN K2 l1 a1 b1 gX1 gK1 Q1 : S → ℝ}
    {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hG0 : rx_HasPartials G gX0 gK0 (K1 - (1 - δ) * Kt, Kt))
    (hΦ0 : rx_HasPartials Φ a0 b0 (G (K1 - (1 - δ) * Kt, Kt), Kt))
    (hG1 : ∀ s, rx_HasPartials G (gX1 s) (gK1 s) (K2 s - (1 - δ) * K1, K1))
    (hΦ1 : ∀ s, rx_HasPartials Φ (a1 s) (b1 s) (G (K2 s - (1 - δ) * K1, K1), K1))
    (hQ0 : Q0 * a0 = 1) (hQ1 : ∀ s, Q1 s * a1 s = 1)
    (hU0 : HasDerivAt U0 l0 (yt - G (K1 - (1 - δ) * Kt, Kt)))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (R s * K1 + wN s - G (K2 s - (1 - δ) * K1, K1)))
    (hmax : IsLocalMax (fun k => U0 (yt - G (k - (1 - δ) * Kt, Kt)) + β * ∑ s,
      T.cp h s * U1 s (R s * k + wN s - G (K2 s - (1 - δ) * k, k))) K1) :
    l0 * Q0 = β * rx_Es T h (fun s => l1 s * (R s + Q1 s * (1 - δ + b1 s))) :=
  rx_uzawa_euler T h hΦG (y1 := fun s k => R s * k + wN s) hG0 hΦ0 hG1 hΦ1 hQ0 hQ1
    (fun s => by simpa using ((hasDerivAt_id K1).const_mul (R s)).add_const (wN s)) hU0 hU1 hmax

/-- Miao, (14.47), p. 497: the firm's static problem `max zF(K, N) − R_kK − wN`; at an
interior maximum `R_k = zF_K(K, N)` and `w = zF_N(K, N)`. -/
theorem eq_14_47_foc {F : ℝ × ℝ → ℝ} {z K N R w FK FN : ℝ} (hF : rx_HasPartials F FK FN (K, N))
    (hK : IsLocalMax (fun k => z * F (k, N) - R * k - w * N) K)
    (hN : IsLocalMax (fun n => z * F (K, n) - R * K - w * n) N) : R = z * FK ∧ w = z * FN := by
  constructor
  · have d : HasDerivAt (fun k => z * F (k, N) - R * k - w * N) (z * FK - R * 1 - 0) K :=
      (((hF.fst).const_mul z).sub ((hasDerivAt_id K).const_mul R)).sub (hasDerivAt_const K _)
    have := hK.hasDerivAt_eq_zero d
    linarith
  · have d : HasDerivAt (fun n => z * F (K, n) - R * K - w * n) (z * FN - 0 - w * 1) N :=
      (((hF.snd).const_mul z).sub (hasDerivAt_const N _)).sub ((hasDerivAt_id N).const_mul w)
    have := hN.hasDerivAt_eq_zero d
    linarith

/-- Miao, p. 497, decentralisation 2: the household's `ψ_{t+1}` condition
`Λₜ(Vₜ − Dₜ) = βEₜΛ_{t+1}V_{t+1}`, from perturbing the share holding `ψ_{t+1} = x` in
`Cₜ = yₜ − x(Vₜ − Dₜ)` and `C_{t+1}(s) = y_{t+1}(s) + xV_{t+1}(s)`. -/
theorem rx_dec2_shares {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {β y0 V D ψ l0 : ℝ} {y1 V1 l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hU0 : HasDerivAt U0 l0 (y0 - ψ * (V - D)))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (y1 s + ψ * V1 s))
    (hmax : IsLocalMax (fun x => U0 (y0 - x * (V - D)) + β * ∑ s,
      T.cp h s * U1 s (y1 s + x * V1 s)) ψ) :
    l0 * (V - D) = β * rx_Es T h (fun s => l1 s * V1 s) := by
  have hc0 : HasDerivAt (fun x => y0 - x * (V - D)) (0 - 1 * (V - D)) ψ :=
    (hasDerivAt_const ψ y0).sub ((hasDerivAt_id ψ).mul_const _)
  have hc1 : ∀ s, HasDerivAt (fun x => y1 s + x * V1 s) (1 * V1 s) ψ :=
    fun s => ((hasDerivAt_id ψ).mul_const _).const_add _
  have e := rx_node_foc (c0 := fun x => y0 - x * (V - D)) (c1 := fun s x => y1 s + x * V1 s)
    hU0 hc0 hU1 hc1 hmax
  simp only [one_mul] at e
  simp only [rx_Es]
  linarith

/-- Miao, p. 497, decentralisation 2: the household's `B_{t+1}` condition
`Λₜ = βEₜΛ_{t+1}R_{f,t+1}`, from perturbing the bond holding `B_{t+1} = x` in `Cₜ = yₜ − x`
and `C_{t+1}(s) = y_{t+1}(s) + xR_f(s)`. -/
theorem rx_dec2_bonds {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {β y0 B l0 : ℝ} {y1 Rf l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hU0 : HasDerivAt U0 l0 (y0 - B)) (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (y1 s + B * Rf s))
    (hmax : IsLocalMax (fun x => U0 (y0 - x) + β * ∑ s, T.cp h s * U1 s (y1 s + x * Rf s)) B) :
    l0 = β * rx_Es T h (fun s => l1 s * Rf s) := by
  have hc0 : HasDerivAt (fun x => y0 - x) (0 - 1) B := (hasDerivAt_const B y0).sub
    (hasDerivAt_id B)
  have hc1 : ∀ s, HasDerivAt (fun x => y1 s + x * Rf s) (1 * Rf s) B :=
    fun s => ((hasDerivAt_id B).mul_const _).const_add _
  have e := rx_node_foc (c0 := fun x => y0 - x) (c1 := fun s x => y1 s + x * Rf s)
    hU0 hc0 hU1 hc1 hmax
  simp only [one_mul] at e
  simp only [rx_Es]
  linarith

/-- Miao, (14.48), p. 498: the firm's `Iₜ` condition `QₜΦ_I(Iₜ, Kₜ) = 1`. The firm's
Lagrangian has the terms `(βᵗΛₜ/Λ₀)(−Iₜ + QₜΦ(Iₜ, Kₜ))` in `Iₜ` (the multiplier on (14.42)
being `Qₜβᵗ Λₜ/Λ₀`); with `βᵗΛₜ/Λ₀ ≠ 0` stationarity is (14.48). -/
theorem eq_14_48 {Φ : ℝ × ℝ → ℝ} {β Λt Λ0 Q I K a : ℝ} {t : ℕ} (hβ : β ≠ 0) (hΛt : Λt ≠ 0)
    (hΛ0 : Λ0 ≠ 0) (hΦ : HasDerivAt (fun x => Φ (x, K)) a I) :
    HasDerivAt (fun x => β ^ t * Λt / Λ0 * -x + β ^ t * Λt / Λ0 * Q * Φ (x, K))
      (β ^ t * Λt / Λ0 * (Q * a - 1)) I ∧
    (β ^ t * Λt / Λ0 * (Q * a - 1) = 0 ↔ Q * a = 1) :=
  rx_invest_foc (Λ := β ^ t * Λt / Λ0) hΦ |>.imp id fun h =>
    h (div_ne_zero (mul_ne_zero (pow_ne_zero t hβ) hΛt) hΛ0)

/-- Miao, (14.49), p. 498: the firm's `K_{t+1}` condition
`ΛₜQₜ = βEₜΛ_{t+1}[z_{t+1}F_K(K_{t+1}, N_{t+1}) + Q_{t+1}(1 − δ + Φ_K(I_{t+1}, K_{t+1}))]`.
The firm maximises `E Σ βᵗ(Λₜ/Λ₀)Dₜ` with `Dₜ = zₜF(Kₜ, Nₜ) − wₜNₜ − Iₜ`; the terms in
`K_{t+1} = k` are, after division by `βᵗ/Λ₀ > 0`, `ΛₜDₜ(k) + βEₜΛ_{t+1}D_{t+1}(k)`. -/
theorem eq_14_49 {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {Φ G F : ℝ × ℝ → ℝ} (hΦG : ∀ X K, Φ (G (X, K), K) = X)
    {δ β Kt K1 yt Λt a0 b0 gX0 gK0 Q0 : ℝ} {z N wN FK K2 Λ1 a1 b1 gX1 gK1 Q1 : S → ℝ}
    (hG0 : rx_HasPartials G gX0 gK0 (K1 - (1 - δ) * Kt, Kt))
    (hΦ0 : rx_HasPartials Φ a0 b0 (G (K1 - (1 - δ) * Kt, Kt), Kt))
    (hG1 : ∀ s, rx_HasPartials G (gX1 s) (gK1 s) (K2 s - (1 - δ) * K1, K1))
    (hΦ1 : ∀ s, rx_HasPartials Φ (a1 s) (b1 s) (G (K2 s - (1 - δ) * K1, K1), K1))
    (hQ0 : Q0 * a0 = 1) (hQ1 : ∀ s, Q1 s * a1 s = 1)
    (hF : ∀ s, HasDerivAt (fun k => F (k, N s)) (FK s) K1)
    (hmax : IsLocalMax (fun k => Λt * (yt - G (k - (1 - δ) * Kt, Kt)) + β * ∑ s,
      T.cp h s * (Λ1 s * (z s * F (k, N s) - wN s - G (K2 s - (1 - δ) * k, k)))) K1) :
    Λt * Q0 = β * rx_Es T h (fun s => Λ1 s * (z s * FK s + Q1 s * (1 - δ + b1 s))) :=
  rx_uzawa_euler T h hΦG (U0 := fun d => Λt * d) (U1 := fun s d => Λ1 s * d)
    (y1 := fun s k => z s * F (k, N s) - wN s) hG0 hΦ0 hG1 hΦ1 hQ0 hQ1
    (fun s => by simpa using ((hF s).const_mul (z s)).sub_const (wN s))
    (by simpa using (hasDerivAt_id _).const_mul Λt)
    (fun s => by simpa using (hasDerivAt_id _).const_mul (Λ1 s)) hmax

/-- Miao, p. 499, decentralisation 3: the capital goods producer maximises
`QₜK_{t+1} − Qₜ(1 − δ)Kₜ − Iₜ` subject to (14.42), i.e. `QₜΦ(Iₜ, Kₜ) − Iₜ`; at an interior
maximum `QₜΦ_I(Iₜ, Kₜ) = 1`. -/
theorem rx_dec3_producer {Φ : ℝ × ℝ → ℝ} {δ Q I K a : ℝ}
    (hΦ : HasDerivAt (fun x => Φ (x, K)) a I)
    (hmax : IsLocalMax (fun x => Q * ((1 - δ) * K + Φ (x, K)) - Q * (1 - δ) * K - x) I) :
    Q * a = 1 := by
  have d : HasDerivAt (fun x => Q * ((1 - δ) * K + Φ (x, K)) - Q * (1 - δ) * K - x)
      (Q * (0 + a) - 0 - 1) I :=
    ((((hasDerivAt_const I _).add hΦ).const_mul Q).sub (hasDerivAt_const I _)).sub
      (hasDerivAt_id I)
  have := hmax.hasDerivAt_eq_zero d
  linarith

/-- Miao, p. 500, decentralisation 3: the household's `K_{t+1}` condition. The household buys
`K_{t+1} = k` at the price `Qₜ` and next period earns `ρ_{t+1}k`; perturbing `k` in
`Cₜ = yₜ − Qₜk`, `C_{t+1}(s) = y_{t+1}(s) + ρ(s)k` gives `ΛₜQₜ = βEₜΛ_{t+1}ρ_{t+1}`. In the
book's budget `Cₜ + QₜK_{t+1} = Qₜ(1 − δ)Kₜ + R_{kt}Kₜ + wₜNₜ + Πₜ`,
`ρ = R_k + (1 − δ)Q`. -/
theorem rx_dec3_euler {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {β y0 Q K1 l0 : ℝ} {y1 ρ l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hU0 : HasDerivAt U0 l0 (y0 - Q * K1)) (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (y1 s + ρ s * K1))
    (hmax : IsLocalMax (fun k => U0 (y0 - Q * k) + β * ∑ s, T.cp h s * U1 s (y1 s + ρ s * k))
      K1) :
    l0 * Q = β * rx_Es T h (fun s => l1 s * ρ s) := by
  have hc0 : HasDerivAt (fun k => y0 - Q * k) (0 - Q * 1) K1 :=
    (hasDerivAt_const K1 y0).sub ((hasDerivAt_id K1).const_mul Q)
  have hc1 : ∀ s, HasDerivAt (fun k => y1 s + ρ s * k) (ρ s * 1) K1 :=
    fun s => ((hasDerivAt_id K1).const_mul _).const_add _
  have e := rx_node_foc (c0 := fun k => y0 - Q * k) (c1 := fun s k => y1 s + ρ s * k)
    hU0 hc0 hU1 hc1 hmax
  simp only [mul_one] at e
  simp only [rx_Es]
  linarith

/-- **Exercise 14.5** (Miao, p. 508), decentralisation 1. With the firm's prices
`R_k = zF_K`, `w = zF_N` (`eq_14_47_foc`) and `Λ = u_C`, the household's conditions
(`rx_dec1_labour`, `rx_dec1_euler`, `rx_invest_foc`) are the planner's (14.45). -/
theorem ex_14_5_dec1 {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {δ β l0 Q0 : ℝ}
    {R z FK l1 Q1 b1 : S → ℝ} (hR : ∀ s, R s = z s * FK s) {uN w zt FNt : ℝ}
    (hw : w = zt * FNt) :
    (l0 * Q0 = β * rx_Es T h (fun s => l1 s * (R s + Q1 s * (1 - δ + b1 s))) ↔
      l0 * Q0 = β * rx_Es T h (fun s => l1 s * (z s * FK s + Q1 s * (1 - δ + b1 s)))) ∧
    (-uN = l0 * w ↔ -uN = l0 * (zt * FNt)) := by
  exact ⟨by simp only [hR], by rw [hw]⟩

/-- **Exercise 14.5** (Miao, p. 508), decentralisation 2. The firm discounts with the
household's `Λ = u_C`; the firm's (14.48)–(14.49) and the household's labour condition with the
firm's wage `w = zF_N` are the planner's (14.45), so the planner's allocation satisfies them
with the same `Q`. The household's share condition then prices the firm,
`Pₜ = Vₜ − Dₜ = EₜβΛ_{t+1}V_{t+1}/Λₜ`. -/
theorem ex_14_5_dec2 {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {β l0 V D : ℝ}
    {l1 V1 : S → ℝ} (hl0 : 0 < l0)
    (hshare : l0 * (V - D) = β * rx_Es T h (fun s => l1 s * V1 s)) :
    V - D = rx_Es T h (fun s => β * l1 s / l0 * V1 s) := by
  have : rx_Es T h (fun s => β * l1 s / l0 * V1 s) =
      β / l0 * rx_Es T h (fun s => l1 s * V1 s) := by
    rw [← rx_Es_mul_left]
    congr 1
    funext s
    ring
  rw [this]
  field_simp
  linarith

/-- **Exercise 14.5** (Miao, p. 508): in each decentralisation the household's budget is the
resource constraint (14.44) `Cₜ + Iₜ = zₜF(Kₜ, Nₜ)`, when `F` is linearly homogeneous and
`R_k = zF_K`, `w = zF_N`. (1) `C + I = R_kK + wN` (14.46); (2) `C + ψ'(V − D) + B' =
ψV + BR_f + wN` with `ψ = ψ' = 1`, `B = B' = 0` and `D = zF − wN − I`; (3)
`C + QK' = Q(1 − δ)K + R_kK + wN + Π` with the producers' profit
`Π = QK' − Q(1 − δ)K − I`. -/
theorem ex_14_5_budgets {F : ℝ × ℝ → ℝ} {z K N FK FN R w C I V Rf Q K' δ : ℝ}
    (hhom : ∀ l : ℝ, 0 < l → F (l * K, l * N) = l * F (K, N))
    (hF : rx_HasPartials F FK FN (K, N)) (hR : R = z * FK) (hw : w = z * FN) :
    (C + I = R * K + w * N → C + I = z * F (K, N)) ∧
    (C + 1 * (V - (z * F (K, N) - w * N - I)) + 0 = 1 * V + 0 * Rf + w * N →
      C + I = z * F (K, N)) ∧
    (C + Q * K' = Q * (1 - δ) * K + R * K + w * N + (Q * K' - Q * (1 - δ) * K - I) →
      C + I = z * F (K, N)) := by
  have he := rx_euler_homog hhom hF
  have hinc : R * K + w * N = z * F (K, N) := by rw [hR, hw, he]; ring
  refine ⟨fun h1 => by rw [h1, hinc], fun h2 => by linarith, fun h3 => by linarith⟩

/-- **Exercise 14.5** (Miao, p. 508), **correction** for decentralisation 3. With the book's
budget the household's return on capital is `ρ = R_k + (1 − δ)Q` (`rx_dec3_euler`): the
household does not internalise that its capital `K_{t+1}` raises the capital producers' output
`Φ(I_{t+1}, K_{t+1})`. Given its Euler equation and `β ≠ 0`, the planner's (14.45) holds iff
`Eₜ[Λ_{t+1}Q_{t+1}Φ_K(I_{t+1}, K_{t+1})] = 0`. -/
theorem ex_14_5_dec3_iff {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {δ β l0 Q0 : ℝ}
    {R l1 Q1 b1 : S → ℝ} (hβ : β ≠ 0)
    (hdec3 : l0 * Q0 = β * rx_Es T h (fun s => l1 s * (R s + (1 - δ) * Q1 s))) :
    l0 * Q0 = β * rx_Es T h (fun s => l1 s * (R s + Q1 s * (1 - δ + b1 s))) ↔
      rx_Es T h (fun s => l1 s * Q1 s * b1 s) = 0 := by
  have e : rx_Es T h (fun s => l1 s * (R s + Q1 s * (1 - δ + b1 s))) =
      rx_Es T h (fun s => l1 s * (R s + (1 - δ) * Q1 s)) +
        rx_Es T h (fun s => l1 s * Q1 s * b1 s) := by
    rw [← rx_Es_add]
    congr 1
    funext s
    ring
  rw [e, hdec3]
  constructor
  · intro h1
    have : β * rx_Es T h (fun s => l1 s * Q1 s * b1 s) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hβ
  · intro h1
    rw [h1]
    ring

/-- The conditional expectation of a strictly positive quantity is strictly positive. -/
theorem rx_Es_pos {S : Type*} [Fintype S] (T : RXTree S) (h : List S) {f : S → ℝ}
    (hf : ∀ s, 0 < f s) : 0 < rx_Es T h f := by
  unfold rx_Es
  obtain ⟨s, hs⟩ : ∃ s, 0 < T.cp h s := by
    by_contra hc
    push Not at hc
    have : ∑ s, T.cp h s ≤ 0 := Finset.sum_nonpos fun s _ => hc s
    rw [T.cp_sum] at this
    linarith
  exact Finset.sum_pos' (fun s _ => mul_nonneg (T.cp_nonneg h s) (hf s).le)
    ⟨s, Finset.mem_univ _, mul_pos hs (hf s)⟩

/-- **Exercise 14.5** (Miao, p. 508), **counterexample** for decentralisation 3: if
`Λ_{t+1}Q_{t+1}Φ_K(I_{t+1}, K_{t+1}) > 0` at every successor (e.g. (14.43) with investment
above its steady-state rate, `rx_Phi_K_pos`, `rx_phiQuad_K`) and `β > 0`, the household's
Euler equation of decentralisation 3 and the planner's (14.45) cannot both hold at the same
allocation and prices: the third decentralisation does not yield the planner's allocation. -/
theorem ex_14_5_dec3_counterexample {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {δ β l0 Q0 : ℝ} {R l1 Q1 b1 : S → ℝ} (hβ : 0 < β) (hpos : ∀ s, 0 < l1 s * Q1 s * b1 s)
    (hdec3 : l0 * Q0 = β * rx_Es T h (fun s => l1 s * (R s + (1 - δ) * Q1 s)))
    (hplan : l0 * Q0 = β * rx_Es T h (fun s => l1 s * (R s + Q1 s * (1 - δ + b1 s)))) :
    False := by
  have := (ex_14_5_dec3_iff T h hβ.ne' hdec3).1 hplan
  linarith [rx_Es_pos T h hpos]

/-- **Exercise 14.5** (Miao, p. 508), corrected decentralisation 3: if the household's capital
also earns the capital producers' rent `Q_{t+1}Φ_K(I_{t+1}, K_{t+1})K_{t+1}` (so its return is
`ρ = R_k + Q(1 − δ + Φ_K)`; when `Φ` is linearly homogeneous and `QΦ_I = 1` this rent is the
producers' whole profit, `rx_producer_profit`), its Euler equation is the planner's (14.45); in
particular the book's version is right when `Φ_K ≡ 0`, e.g. `Φ(I, K) = vI`. -/
theorem ex_14_5_dec3_corrected {S : Type*} [Fintype S] (T : RXTree S) (h : List S)
    {δ β y0 Q K1 l0 : ℝ} {y1 R Q1 b1 l1 : S → ℝ} {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ}
    (hU0 : HasDerivAt U0 l0 (y0 - Q * K1))
    (hU1 : ∀ s, HasDerivAt (U1 s) (l1 s) (y1 s + (R s + Q1 s * (1 - δ + b1 s)) * K1))
    (hmax : IsLocalMax (fun k => U0 (y0 - Q * k) + β * ∑ s,
      T.cp h s * U1 s (y1 s + (R s + Q1 s * (1 - δ + b1 s)) * k)) K1) :
    l0 * Q = β * rx_Es T h (fun s => l1 s * (R s + Q1 s * (1 - δ + b1 s))) ∧
      ((∀ s, b1 s = 0) → ∀ s, R s + Q1 s * (1 - δ + b1 s) = R s + (1 - δ) * Q1 s) :=
  ⟨rx_dec3_euler T h hU0 hU1 hmax, fun hb s => by rw [hb s]; ring⟩

/-- The rent of the capital producers: with `Φ` linearly homogeneous and `QΦ_I = 1`, the
profit `QΦ(I, K) − I` equals `QΦ_K K`. -/
theorem rx_producer_profit {Φ : ℝ × ℝ → ℝ} {Q I K a b : ℝ}
    (hhom : ∀ l : ℝ, 0 < l → Φ (l * I, l * K) = l * Φ (I, K))
    (hd : rx_HasPartials Φ a b (I, K)) (hQ : Q * a = 1) : Q * Φ (I, K) - I = Q * b * K := by
  rw [rx_euler_homog hhom hd]
  linear_combination I * hQ

end Miao.NeoclassicalGrowth
