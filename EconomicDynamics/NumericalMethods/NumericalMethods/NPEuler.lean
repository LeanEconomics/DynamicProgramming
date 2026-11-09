/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Euler equations from the Bellman equation: the growth model and Exercise 11.3

Miao, *Economic Dynamics in Discrete Time*, (11.8)–(11.9) (pp. 374, 377) and
Exercise 11.3 (p. 384).

From the Bellman equation (11.9) `V(K, z) = max_{K'} u(f(K, z) − K') +
βE[V(K', z') | z]`, attained by an interior policy `K' = g(K, z)`, with `V`
differentiable in `K` and differentiation under the conditional expectation
allowed, the first-order condition and the envelope (Benveniste–Scheinkman)
condition give the Euler equation (11.8) (`eq_11_8`). The envelope step is
`np_envelope`: a differentiable function that dominates another near a point,
with equality there, has the same derivative.

Exercise 11.3 adds endogenous labour: `U(C, N) = (C^θ(1 − N)^{1−θ})^{1−γ}/(1 − γ)`
and `C + K' = (1 − δ)K + zK^αN^{1−α}`. We compute the marginal utilities and
products (`ex_11_3_UC`, `ex_11_3_FK`, `ex_11_3_FN`, `ex_11_3_total_N`) and derive
from the Bellman equation the intratemporal condition
`(1 − θ)C = θ(1 − N)(1 − α)zK^αN^{−α}` (`ex_11_3_intratemporal`), the capital
first-order condition and envelope condition, the Euler equation
`U_C(C, N) = βE[U_C(C', N')(1 − δ + αz'K'^{α−1}N'^{1−α})]` (`ex_11_3_euler`), and the
deterministic steady-state capital–labour ratio (`ex_11_3_steady_state`).

The conditional law of `z'` given `z` is an arbitrary family of measures `Q z`
(for the AR(1) of the book, the image of the standard normal under
`ε ↦ exp(ρ ln z + σε)`); differentiability of `K' ↦ E[V(K', z') | z]` with
derivative `E[V_K(K', z') | z]` is a hypothesis (it holds under the usual
domination conditions). The numerical solutions asked for in Exercise 11.3
(a)–(e) are computational and not formalised.
-/

namespace Miao.NumericalMethods.NP

open Filter Topology MeasureTheory

/-- The envelope step (Benveniste–Scheinkman): if `W ≤ V` near `K₀` with equality at `K₀`, and
both are differentiable at `K₀`, their derivatives agree. -/
theorem np_envelope {V W : ℝ → ℝ} {K0 V' W' : ℝ} (hle : ∀ᶠ K in 𝓝 K0, W K ≤ V K)
    (heq : W K0 = V K0) (hV : HasDerivAt V V' K0) (hW : HasDerivAt W W' K0) : V' = W' := by
  have hmin : IsLocalMin (fun K => V K - W K) K0 := by
    filter_upwards [hle] with K hK
    rw [heq, sub_self]
    linarith
  have := hmin.hasDerivAt_eq_zero (hV.sub hW)
  linarith

/-- **(11.8)** (Miao, p. 374), derived from the Bellman equation (11.9): if `g(K, z)` attains the
maximum in (11.9) in the interior `0 < g < f`, `u` is differentiable at positive consumption,
`f`, `V` are differentiable in `K` and `K' ↦ E[V(K', z')|z]` has derivative `E[V_K(K', z')|z]`,
then the first-order condition `u'(C) = βE[V_K(K', z')|z]`, the envelope condition
`V_K(K, z) = u'(C) f_K(K, z)` and the Euler equation
`u'(f(K, z) − g(K, z)) = βE[u'(f(K', z') − g(K', z')) f_K(K', z') | z]`, `K' = g(K, z)`, hold. -/
theorem eq_11_8 {u up : ℝ → ℝ} {f fK V VK g : ℝ → ℝ → ℝ} {β : ℝ} {Q : ℝ → Measure ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt u (up c) c)
    (hf : ∀ K z, HasDerivAt (fun K => f K z) (fK K z) K)
    (hV : ∀ K z, HasDerivAt (fun K => V K z) (VK K z) K)
    (hW : ∀ k z, HasDerivAt (fun k => ∫ z', V k z' ∂Q z) (∫ z', VK k z' ∂Q z) k)
    (hBell : ∀ K z k, 0 < k → k < f K z → u (f K z - k) + β * ∫ z', V k z' ∂Q z ≤ V K z)
    (hg : ∀ K z, 0 < g K z ∧ g K z < f K z ∧
      V K z = u (f K z - g K z) + β * ∫ z', V (g K z) z' ∂Q z) (K z : ℝ) :
    up (f K z - g K z) = β * ∫ z', VK (g K z) z' ∂Q z ∧
      VK K z = up (f K z - g K z) * fK K z ∧
        up (f K z - g K z) =
          β * ∫ z', up (f (g K z) z' - g (g K z) z') * fK (g K z) z' ∂Q z := by
  -- first-order condition at every state
  have foc : ∀ K z, up (f K z - g K z) = β * ∫ z', VK (g K z) z' ∂Q z := by
    intro K z
    obtain ⟨h0, h1, heq⟩ := hg K z
    have hc : 0 < f K z - g K z := sub_pos.2 h1
    have hd : HasDerivAt (fun k => u (f K z - k) + β * ∫ z', V k z' ∂Q z)
        (up (f K z - g K z) * (-1) + β * ∫ z', VK (g K z) z' ∂Q z) (g K z) := by
      have h2 := (hu _ hc).comp (g K z) ((hasDerivAt_id' (g K z)).const_sub (f K z))
      exact h2.add ((hW (g K z) z).const_mul β)
    have hmax : IsLocalMax (fun k => u (f K z - k) + β * ∫ z', V k z' ∂Q z) (g K z) := by
      filter_upwards [Ioo_mem_nhds h0 h1] with k hk
      rw [← heq]
      exact hBell K z k hk.1 hk.2
    have := hmax.hasDerivAt_eq_zero hd
    linarith
  -- envelope condition at every state
  have env : ∀ K z, VK K z = up (f K z - g K z) * fK K z := by
    intro K z
    obtain ⟨h0, h1, heq⟩ := hg K z
    have hc : 0 < f K z - g K z := sub_pos.2 h1
    have hlow : HasDerivAt (fun K' => u (f K' z - g K z) + β * ∫ z', V (g K z) z' ∂Q z)
        (up (f K z - g K z) * fK K z) K := by
      have h2 := (hu _ hc).comp K ((hf K z).sub_const (g K z))
      simpa using h2.add_const (β * ∫ z', V (g K z) z' ∂Q z)
    have hev : ∀ᶠ K' in 𝓝 K, g K z < f K' z :=
      (hf K z).continuousAt.eventually (lt_mem_nhds h1)
    refine np_envelope ?_ heq.symm (hV K z) hlow
    filter_upwards [hev] with K' hK'
    exact hBell K' z (g K z) h0 hK'
  refine ⟨foc K z, env K z, ?_⟩
  rw [foc K z]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun z' => env (g K z) z')

/-! ### Exercise 11.3: endogenous labour -/

/-- Exercise 11.3 (Miao, p. 384): period utility `U(C, N) = (C^θ(1 − N)^{1−θ})^{1−γ}/(1 − γ)`. -/
noncomputable def np_ex3U (θ γ C N : ℝ) : ℝ := (C ^ θ * (1 - N) ^ (1 - θ)) ^ (1 - γ) / (1 - γ)

/-- Exercise 11.3: output plus undepreciated capital `(1 − δ)K + zK^αN^{1−α}`. -/
noncomputable def np_ex3F (α δ K N z : ℝ) : ℝ := (1 - δ) * K + z * K ^ α * N ^ (1 - α)

/-- The composite `X = C^θ(1 − N)^{1−θ}`. -/
noncomputable def np_ex3X (θ C N : ℝ) : ℝ := C ^ θ * (1 - N) ^ (1 - θ)

theorem np_ex3X_pos {θ C N : ℝ} (hC : 0 < C) (hN : N < 1) : 0 < np_ex3X θ C N :=
  mul_pos (Real.rpow_pos_of_pos hC θ) (Real.rpow_pos_of_pos (sub_pos.2 hN) _)

/-- Exercise 11.3: `U_C(C, N) = θX^{1−γ}/C`. -/
theorem ex_11_3_UC {θ γ C N : ℝ} (hγ : γ ≠ 1) (hC : 0 < C) (hN : N < 1) :
    HasDerivAt (fun C => np_ex3U θ γ C N) (θ * np_ex3X θ C N ^ (1 - γ) / C) C := by
  have hX := np_ex3X_pos (θ := θ) hC hN
  have hg : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h1 : HasDerivAt (fun C => C ^ θ * (1 - N) ^ (1 - θ))
      (θ * C ^ (θ - 1) * (1 - N) ^ (1 - θ)) C :=
    (Real.hasDerivAt_rpow_const (Or.inl hC.ne')).mul_const _
  have h2 := (h1.rpow_const (p := 1 - γ) (Or.inl hX.ne')).div_const (1 - γ)
  unfold np_ex3U
  convert h2 using 1
  have ha : 0 < (1 - N) ^ (1 - θ) := Real.rpow_pos_of_pos (sub_pos.2 hN) _
  unfold np_ex3X at hX ⊢
  rw [Real.rpow_sub_one hC.ne', Real.rpow_sub_one hX.ne']
  field_simp

/-- Exercise 11.3: `F_K = 1 − δ + αzK^{α−1}N^{1−α}`. -/
theorem ex_11_3_FK {α δ K N z : ℝ} (hK : 0 < K) :
    HasDerivAt (fun K => np_ex3F α δ K N z) (1 - δ + α * z * K ^ (α - 1) * N ^ (1 - α)) K := by
  have h := ((hasDerivAt_id' K).const_mul (1 - δ)).add
    (((Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul z).mul_const (N ^ (1 - α)))
  unfold np_ex3F
  convert h using 1
  ring

/-- Exercise 11.3: `F_N = (1 − α)zK^αN^{−α}`. -/
theorem ex_11_3_FN {α δ K N z : ℝ} (hN : 0 < N) :
    HasDerivAt (fun N => np_ex3F α δ K N z) ((1 - α) * z * K ^ α * N ^ (-α)) N := by
  have h := (hasDerivAt_const N ((1 - δ) * K)).add
    ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul (z * K ^ α))
  unfold np_ex3F
  convert h using 1
  rw [show 1 - α - 1 = -α by ring]
  ring

/-- Exercise 11.3, the total derivative in `N` of `U(C(N), N)` when `C` depends on `N` with
`C'(N) = c'`: it is `U_C c' + U_N = X^{1−γ}(θc'/C − (1 − θ)/(1 − N))`. -/
theorem ex_11_3_total_N {θ γ : ℝ} (hγ : γ ≠ 1) {Cf : ℝ → ℝ} {c' N : ℝ} (hCf : HasDerivAt Cf c' N)
    (hC : 0 < Cf N) (hN : N < 1) :
    HasDerivAt (fun N => np_ex3U θ γ (Cf N) N)
      (np_ex3X θ (Cf N) N ^ (1 - γ) * (θ * c' / Cf N - (1 - θ) / (1 - N))) N := by
  have hX := np_ex3X_pos (θ := θ) hC hN
  have hg : (1 - γ) ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  have h1N : 0 < 1 - N := sub_pos.2 hN
  have ha := hCf.rpow_const (p := θ) (Or.inl hC.ne')
  have hb := ((hasDerivAt_id' N).const_sub 1).rpow_const (p := 1 - θ) (Or.inl h1N.ne')
  have h2 := ((ha.mul hb).rpow_const (p := 1 - γ) (Or.inl hX.ne')).div_const (1 - γ)
  unfold np_ex3U
  convert h2 using 1
  simp only [Pi.mul_apply]
  unfold np_ex3X at hX ⊢
  rw [Real.rpow_sub_one hC.ne', Real.rpow_sub_one h1N.ne', Real.rpow_sub_one hX.ne']
  field_simp
  ring

/-- **Exercise 11.3** (Miao, p. 384), the first-order conditions and the Euler equation. Let `V`
solve the Bellman equation
`V(K, z) = max_{K', N} U((1 − δ)K + zK^αN^{1−α} − K', N) + βE[V(K', z') | z]`
with the maximum attained by an interior policy `(g_K, g_N)` (`K' > 0`, `0 < N < 1`, `C > 0`),
`V` differentiable in `K` and `K' ↦ E[V(K', z')|z]` with derivative `E[V_K(K', z')|z]`. Then, with
`C = F(K, N, z) − K'`, (i) the intratemporal condition `(1 − θ)C = θ(1 − N)(1 − α)zK^αN^{−α}`,
(ii) the capital first-order condition `U_C(C, N) = βE[V_K(K', z')|z]`, (iii) the envelope
condition `V_K(K, z) = U_C(C, N)(1 − δ + αzK^{α−1}N^{1−α})` and (iv) the Euler equation
`U_C(C, N) = βE[U_C(C', N')(1 − δ + αz'K'^{α−1}N'^{1−α}) | z]` hold. -/
theorem ex_11_3_euler {θ γ α δ β : ℝ} (hγ : γ ≠ 1) {V VK gK gN : ℝ → ℝ → ℝ}
    {Q : ℝ → Measure ℝ}
    (hV : ∀ K z, 0 < K → HasDerivAt (fun K => V K z) (VK K z) K)
    (hW : ∀ k z, HasDerivAt (fun k => ∫ z', V k z' ∂Q z) (∫ z', VK k z' ∂Q z) k)
    (hBell : ∀ K z k N, 0 < k → 0 < N → N < 1 → 0 < np_ex3F α δ K N z - k →
      np_ex3U θ γ (np_ex3F α δ K N z - k) N + β * ∫ z', V k z' ∂Q z ≤ V K z)
    (hg : ∀ K z, 0 < gK K z ∧ 0 < gN K z ∧ gN K z < 1 ∧
      0 < np_ex3F α δ K (gN K z) z - gK K z ∧
      V K z = np_ex3U θ γ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) +
        β * ∫ z', V (gK K z) z' ∂Q z)
    {K z : ℝ} (hK : 0 < K) :
    (1 - θ) * (np_ex3F α δ K (gN K z) z - gK K z) =
        θ * (1 - gN K z) * ((1 - α) * z * K ^ α * gN K z ^ (-α)) ∧
      θ * np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) /
          (np_ex3F α δ K (gN K z) z - gK K z) = β * ∫ z', VK (gK K z) z' ∂Q z ∧
      VK K z = θ * np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) /
          (np_ex3F α δ K (gN K z) z - gK K z) *
            (1 - δ + α * z * K ^ (α - 1) * gN K z ^ (1 - α)) ∧
      θ * np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) /
          (np_ex3F α δ K (gN K z) z - gK K z) =
        β * ∫ z', θ * np_ex3X θ (np_ex3F α δ (gK K z) (gN (gK K z) z') z' - gK (gK K z) z')
            (gN (gK K z) z') ^ (1 - γ) /
              (np_ex3F α δ (gK K z) (gN (gK K z) z') z' - gK (gK K z) z') *
            (1 - δ + α * z' * gK K z ^ (α - 1) * gN (gK K z) z' ^ (1 - α)) ∂Q z := by
  -- (ii) capital first-order condition, at every state
  have focK : ∀ K z, θ * np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) /
      (np_ex3F α δ K (gN K z) z - gK K z) = β * ∫ z', VK (gK K z) z' ∂Q z := by
    intro K z
    obtain ⟨h0, hN0, hN1, hc, heq⟩ := hg K z
    set F0 := np_ex3F α δ K (gN K z) z
    have hd : HasDerivAt (fun k => np_ex3U θ γ (F0 - k) (gN K z) + β * ∫ z', V k z' ∂Q z)
        (θ * np_ex3X θ (F0 - gK K z) (gN K z) ^ (1 - γ) / (F0 - gK K z) * (-1) +
          β * ∫ z', VK (gK K z) z' ∂Q z) (gK K z) := by
      have h2 := (ex_11_3_UC (θ := θ) (N := gN K z) hγ hc hN1).comp (gK K z)
        ((hasDerivAt_id' (gK K z)).const_sub F0)
      exact h2.add ((hW (gK K z) z).const_mul β)
    have hmax : IsLocalMax (fun k => np_ex3U θ γ (F0 - k) (gN K z) + β * ∫ z', V k z' ∂Q z)
        (gK K z) := by
      filter_upwards [Ioo_mem_nhds h0 (sub_pos.1 hc)] with k hk
      rw [← heq]
      exact hBell K z k (gN K z) hk.1 hN0 hN1 (sub_pos.2 hk.2)
    have := hmax.hasDerivAt_eq_zero hd
    linarith
  -- (iii) envelope condition, at every positive capital stock
  have env : ∀ K z, 0 < K → VK K z =
      θ * np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) /
          (np_ex3F α δ K (gN K z) z - gK K z) *
            (1 - δ + α * z * K ^ (α - 1) * gN K z ^ (1 - α)) := by
    intro K z hK
    obtain ⟨h0, hN0, hN1, hc, heq⟩ := hg K z
    have hFK := ex_11_3_FK (α := α) (δ := δ) (N := gN K z) (z := z) hK
    have hlow : HasDerivAt (fun K' => np_ex3U θ γ (np_ex3F α δ K' (gN K z) z - gK K z) (gN K z) +
        β * ∫ z', V (gK K z) z' ∂Q z)
        (θ * np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) /
          (np_ex3F α δ K (gN K z) z - gK K z) *
            (1 - δ + α * z * K ^ (α - 1) * gN K z ^ (1 - α))) K := by
      have h2 := (ex_11_3_UC (θ := θ) (N := gN K z) hγ hc hN1).comp K (hFK.sub_const (gK K z))
      simpa using h2.add_const (β * ∫ z', V (gK K z) z' ∂Q z)
    have hev : ∀ᶠ K' in 𝓝 K, 0 < np_ex3F α δ K' (gN K z) z - gK K z :=
      (hFK.sub_const (gK K z)).continuousAt.eventually (lt_mem_nhds hc)
    refine np_envelope ?_ heq.symm (hV K z hK) hlow
    filter_upwards [hev] with K' hK'
    exact hBell K' z (gK K z) (gN K z) h0 hN0 hN1 hK'
  -- (i) intratemporal condition
  have intra : (1 - θ) * (np_ex3F α δ K (gN K z) z - gK K z) =
      θ * (1 - gN K z) * ((1 - α) * z * K ^ α * gN K z ^ (-α)) := by
    obtain ⟨h0, hN0, hN1, hc, heq⟩ := hg K z
    have hFN := ex_11_3_FN (α := α) (δ := δ) (K := K) (z := z) hN0
    have hd := ex_11_3_total_N (θ := θ) hγ (hFN.sub_const (gK K z)) hc hN1
    have hd' := hd.add_const (β * ∫ z', V (gK K z) z' ∂Q z)
    have hmax : IsLocalMax (fun N => np_ex3U θ γ (np_ex3F α δ K N z - gK K z) N +
        β * ∫ z', V (gK K z) z' ∂Q z) (gN K z) := by
      have hev : ∀ᶠ N in 𝓝 (gN K z), 0 < np_ex3F α δ K N z - gK K z :=
        (hFN.sub_const (gK K z)).continuousAt.eventually (lt_mem_nhds hc)
      filter_upwards [hev, Ioo_mem_nhds hN0 hN1] with N hN hN'
      rw [← heq]
      exact hBell K z (gK K z) N h0 hN'.1 hN'.2 hN
    have h0' := hmax.hasDerivAt_eq_zero hd'
    have hX := np_ex3X_pos (θ := θ) hc hN1
    have hXg : 0 < np_ex3X θ (np_ex3F α δ K (gN K z) z - gK K z) (gN K z) ^ (1 - γ) :=
      Real.rpow_pos_of_pos hX _
    have h1N : 0 < 1 - gN K z := sub_pos.2 hN1
    have hbr : θ * ((1 - α) * z * K ^ α * gN K z ^ (-α)) / (np_ex3F α δ K (gN K z) z - gK K z) -
        (1 - θ) / (1 - gN K z) = 0 := by
      rcases mul_eq_zero.1 h0' with h | h
      · exact absurd h hXg.ne'
      · exact h
    field_simp at hbr
    linarith
  refine ⟨intra, focK K z, env K z hK, ?_⟩
  rw [focK K z]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun z' => env (gK K z) z' (hg K z).1)

/-- Exercise 11.3, the deterministic steady state (`z = 1`): the Euler equation at a steady state
`β(1 − δ + α(K/N)^{α−1}) = 1` holds iff `K/N = (α/(1/β − 1 + δ))^{1/(1−α)}`. -/
theorem ex_11_3_steady_state {α β δ x : ℝ} (hα1 : α < 1) (hx : 0 < x) (hβ : 0 < β)
    (hden : 0 < 1 / β - 1 + δ) (hα0 : 0 < α) :
    β * (1 - δ + α * x ^ (α - 1)) = 1 ↔ x = (α / (1 / β - 1 + δ)) ^ (1 / (1 - α)) := by
  have hq : 0 < α / (1 / β - 1 + δ) := div_pos hα0 hden
  have h1α : (1 - α) ≠ 0 := by linarith
  constructor
  · intro h
    have hxa : x ^ (α - 1) = (1 / β - 1 + δ) / α := by
      field_simp
      field_simp at h
      linarith
    have : x = (x ^ (α - 1)) ^ (1 / (α - 1)) := by
      rw [← Real.rpow_mul hx.le, mul_one_div_cancel (by linarith : α - 1 ≠ 0), Real.rpow_one]
    have hd' : 0 < (1 / β - 1 + δ) / α := div_pos hden hα0
    have hα1' : α - 1 ≠ 0 := by linarith
    rw [this, hxa, show α / (1 / β - 1 + δ) = ((1 / β - 1 + δ) / α)⁻¹ by rw [inv_div],
      Real.inv_rpow hd'.le, ← Real.rpow_neg hd'.le]
    congr 1
    field_simp
    ring
  · intro h
    have hxa : x ^ (α - 1) = (1 / β - 1 + δ) / α := by
      rw [h, ← Real.rpow_mul hq.le]
      have : 1 / (1 - α) * (α - 1) = -1 := by field_simp; ring
      rw [this, Real.rpow_neg_one, inv_div]
    rw [hxa]
    field_simp
    ring

end Miao.NumericalMethods.NP
