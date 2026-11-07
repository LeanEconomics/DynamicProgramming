/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# §8.6.1 Neoclassical theory of investment

Miao, §8.6.1, pp. 276–277. A firm with production function `F(K, L)`.

* The rental firm: maximising `Σ βᵗ [F(Kₜ, Lₜ) − wₜLₜ − R_{kt}Kₜ]` reduces to maximising static
  profits period by period (`iv_static_reduction`, for partial sums and for convergent sums), and
  an interior maximum satisfies `F₁ = R_k`, `F₂ = w` (`iv_rental_foc`).
* The owning firm (8.28)–(8.29): the first-order conditions `Qₜ = 1`,
  `Qₜ = β(1 − δ + F₁(K_{t+1}, L_{t+1}))` are derived by perturbing `K_{t+1}` (`eq_8_29_foc`), and
  with `β = 1/(1 + r)` they give `F₁ = r + δ` (`iv_F1_eq_r_add_delta`). The statement "if
  `R_k = r + δ` the two problems give identical solutions" is proved as an exact identity
  (summation by parts): the owning firm's objective up to `T` equals its date-0 terms, plus the
  rental firm's objective at `R_k = r + δ` from date 1 on, minus the terminal term `βᵀK_{T+1}`
  (`iv_owned_partialSum`, `iv_owned_le_of_rental`).
* Operating profit `π(K) = max_L F(K, L) − wL` and the envelope condition `π′(K) = F₁(K, L)`
  (`iv_envelope_profit`).
* The Cobb–Douglas case `F = K^{α_k} L^{α_l}` with `0 < α_l < 1`: the optimal labour
  (`iv_cdLabour`, `iv_cd_max`), the profit formula
  `π(K) = K^{α_k/(1−α_l)} (α_l/w)^{α_l/(1−α_l)} (1 − α_l)` (`iv_cd_profit`), the envelope
  condition (`iv_cd_envelope`), constant returns `π = AK` (`iv_cd_crs`), and convexity /
  concavity of `π` under increasing / decreasing returns (`iv_cd_convex`, `iv_cd_concave`; we
  prove strict convexity / concavity).
-/

namespace Miao.Applications

open Filter Topology

/-- Miao, p. 276: the rental firm's problem reduces to static profit maximisation. If `x t`
maximises the period-`t` profit `f t` for every `t`, then for any other plan `y` and every `T`
the discounted partial sums satisfy `Σ_{t<T} βᵗ f t (y t) ≤ Σ_{t<T} βᵗ f t (x t)`, and the same
holds for convergent infinite sums. -/
theorem iv_static_reduction {X : Type*} {β : ℝ} (hβ : 0 ≤ β) (f : ℕ → X → ℝ) (x : ℕ → X)
    (hx : ∀ t y, f t y ≤ f t (x t)) (y : ℕ → X) :
    (∀ T, ∑ t ∈ Finset.range T, β ^ t * f t (y t) ≤ ∑ t ∈ Finset.range T, β ^ t * f t (x t))
      ∧ ∀ a b, HasSum (fun t => β ^ t * f t (y t)) a →
        HasSum (fun t => β ^ t * f t (x t)) b → a ≤ b := by
  have h : ∀ t, β ^ t * f t (y t) ≤ β ^ t * f t (x t) := fun t =>
    mul_le_mul_of_nonneg_left (hx t (y t)) (pow_nonneg hβ t)
  exact ⟨fun T => Finset.sum_le_sum fun t _ => h t, fun a b ha hb => hasSum_le h ha hb⟩

/-- Miao, p. 276: at an interior maximum `(K, L)` of the rental firm's static profit
`F(K, L) − wL − R_kK`, `F₁(K, L) = R_k` and `F₂(K, L) = w`. -/
theorem iv_rental_foc {F : ℝ → ℝ → ℝ} {w R K L F1 F2 : ℝ}
    (hK : HasDerivAt (fun k => F k L) F1 K) (hL : HasDerivAt (fun l => F K l) F2 L)
    (hmax : IsLocalMax (fun p : ℝ × ℝ => F p.1 p.2 - w * p.2 - R * p.1) (K, L)) :
    F1 = R ∧ F2 = w := by
  have h1 : IsLocalMax (fun k => F k L - w * L - R * k) K := by
    have := hmax.comp_continuous (g := fun k : ℝ => (k, L))
      (Continuous.continuousAt (by fun_prop))
    exact this
  have h2 : IsLocalMax (fun l => F K l - w * l - R * K) L := by
    have := hmax.comp_continuous (g := fun l : ℝ => (K, l))
      (Continuous.continuousAt (by fun_prop))
    exact this
  have d1 : HasDerivAt (fun k => F k L - w * L - R * k) (F1 - 0 - R * 1) K :=
    (hK.sub (hasDerivAt_const K (w * L))).sub ((hasDerivAt_id K).const_mul R)
  have d2 : HasDerivAt (fun l => F K l - w * l - R * K) (F2 - w * 1 - 0) L :=
    (hL.sub ((hasDerivAt_id L).const_mul w)).sub (hasDerivAt_const L (R * K))
  have e1 := h1.hasDerivAt_eq_zero d1
  have e2 := h2.hasDerivAt_eq_zero d2
  constructor <;> linarith

/-- Miao, (8.28)–(8.29) and the first-order conditions, p. 277. Substitute
`Iₜ = K_{t+1} − (1 − δ)Kₜ` and `I_{t+1} = K_{t+2} − (1 − δ)K_{t+1}`: the terms of the objective
that involve `k = K_{t+1}` are
`βᵗ[F(Kₜ, Lₜ) − wₜLₜ − (k − (1 − δ)Kₜ)] + β^{t+1}[F(k, L′) − w′L′ − (K_{t+2} − (1 − δ)k)]`.
If `K_{t+1}` maximises this locally, then `1 = β(1 − δ + F₁(K_{t+1}, L_{t+1}))`, i.e. `Qₜ = 1`
(the first-order condition for `Iₜ`) and `Qₜ = β(1 − δ + F₁)` with `Qₜ = Q_{t+1} = 1`. -/
theorem eq_8_29_foc {F : ℝ → ℝ → ℝ} {β δ w w' Kt Lt L' K2 k F1 : ℝ} {t : ℕ} (hβ : 0 < β)
    (hF : HasDerivAt (fun x => F x L') F1 k)
    (hmax : IsLocalMax (fun x => β ^ t * (F Kt Lt - w * Lt - (x - (1 - δ) * Kt))
      + β ^ (t + 1) * (F x L' - w' * L' - (K2 - (1 - δ) * x))) k) :
    β * (1 - δ + F1) = 1 := by
  have d : HasDerivAt (fun x => β ^ t * (F Kt Lt - w * Lt - (x - (1 - δ) * Kt))
      + β ^ (t + 1) * (F x L' - w' * L' - (K2 - (1 - δ) * x)))
      (β ^ t * (0 - 0 - (1 - 0)) + β ^ (t + 1) * (F1 - 0 - (0 - (1 - δ) * 1))) k := by
    apply HasDerivAt.add
    · exact (((hasDerivAt_const k _).sub (hasDerivAt_const k _)).sub
        ((hasDerivAt_id k).sub (hasDerivAt_const k _))).const_mul _
    · exact ((hF.sub (hasDerivAt_const k _)).sub
        ((hasDerivAt_const k _).sub ((hasDerivAt_id k).const_mul _))).const_mul _
  have e := hmax.hasDerivAt_eq_zero d
  have hbt : 0 < β ^ t := pow_pos hβ t
  rw [pow_succ] at e
  have : β ^ t * (β * (1 - δ + F1) - 1) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h hbt.ne'
  · linarith

/-- Miao, p. 277: with `β = 1/(1 + r)`, the first-order condition `1 = β(1 − δ + F₁)` gives
`F₁(K_{t+1}, L_{t+1}) = r + δ`. -/
theorem iv_F1_eq_r_add_delta {β r δ F1 : ℝ} (hr : -1 < r) (hβ : β = 1 / (1 + r))
    (h : β * (1 - δ + F1) = 1) : F1 = r + δ := by
  have h1 : (1 + r) ≠ 0 := by linarith
  rw [hβ] at h
  field_simp at h
  linarith

/-- The owning firm's partial objective, Miao (8.28)–(8.29): `Σ_{t ≤ T} βᵗ[F(Kₜ, Lₜ) − wₜLₜ − Iₜ]`
with `Iₜ = K_{t+1} − (1 − δ)Kₜ`. -/
noncomputable def iv_ownedObj (F : ℝ → ℝ → ℝ) (β δ : ℝ) (w K L : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (T + 1),
    β ^ t * (F (K t) (L t) - w t * L t - (K (t + 1) - (1 - δ) * K t))

/-- The rental firm's partial objective from date 1 to date `T`, Miao p. 276:
`Σ_{1 ≤ t ≤ T} βᵗ[F(Kₜ, Lₜ) − wₜLₜ − R_kKₜ]`. -/
noncomputable def iv_rentalObj (F : ℝ → ℝ → ℝ) (β Rk : ℝ) (w K L : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T,
    β ^ (t + 1) * (F (K (t + 1)) (L (t + 1)) - w (t + 1) * L (t + 1) - Rk * K (t + 1))

/-- Miao, p. 277: "if the rental rate `R_k` is equal to `r + δ`, then the two problems give
identical solutions". Summation by parts, with `β(1 + r) = 1`: the owning firm's objective
equals its date-0 terms plus the rental firm's objective at `R_k = r + δ`, minus `βᵀK_{T+1}`. -/
theorem iv_owned_partialSum (F : ℝ → ℝ → ℝ) {β r δ : ℝ} (hβ : β * (1 + r) = 1)
    (w K L : ℕ → ℝ) (T : ℕ) :
    iv_ownedObj F β δ w K L T = F (K 0) (L 0) - w 0 * L 0 + (1 - δ) * K 0
      + iv_rentalObj F β (r + δ) w K L T - β ^ T * K (T + 1) := by
  induction T with
  | zero => simp [iv_ownedObj, iv_rentalObj]; ring
  | succ n ih =>
    unfold iv_ownedObj at ih ⊢
    unfold iv_rentalObj at ih ⊢
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have : β ^ n = β ^ (n + 1) * (1 + r) := by rw [pow_succ, mul_assoc, hβ, mul_one]
    rw [this]
    ring

/-- Miao, p. 277: consequence of `iv_owned_partialSum`. If the plan `(K, L)` maximises the
rental firm's static profit with `R_k = r + δ` at every date `t ≥ 1`, then against any other
plan `(K′, L′)` with the same date-0 values, the owning firm's objective up to `T`, corrected by
the terminal value `βᵀK_{T+1}` of the capital left, is at least as large. -/
theorem iv_owned_le_of_rental (F : ℝ → ℝ → ℝ) {β r δ : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β * (1 + r) = 1) (w K L K' L' : ℕ → ℝ) (h0 : K' 0 = K 0) (hL0 : L' 0 = L 0)
    (hmax : ∀ t, 1 ≤ t → ∀ k l, F k l - w t * l - (r + δ) * k ≤
      F (K t) (L t) - w t * L t - (r + δ) * K t) (T : ℕ) :
    iv_ownedObj F β δ w K' L' T + β ^ T * K' (T + 1) ≤
      iv_ownedObj F β δ w K L T + β ^ T * K (T + 1) := by
  rw [iv_owned_partialSum F hβ, iv_owned_partialSum F hβ, h0, hL0]
  have : iv_rentalObj F β (r + δ) w K' L' T ≤ iv_rentalObj F β (r + δ) w K L T :=
    Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
      (hmax (t + 1) (by omega) _ _) (pow_nonneg hβ0 _)
  linarith

/-- Miao, p. 277, the envelope condition `π′(K) = F₁(K, L)`: if `π(K) ≥ F(K, L₀) − wL₀` for all
`K` near `K₀` (as for `π(K) = max_L F(K, L) − wL`), with equality at `K₀` (`L₀` optimal at
`K₀`), and both sides are differentiable at `K₀`, then `π′(K₀) = F₁(K₀, L₀)`. -/
theorem iv_envelope_profit {F : ℝ → ℝ → ℝ} {prof : ℝ → ℝ} {w K₀ L₀ p F1 : ℝ}
    (hle : ∀ᶠ K in 𝓝 K₀, F K L₀ - w * L₀ ≤ prof K) (heq : prof K₀ = F K₀ L₀ - w * L₀)
    (hp : HasDerivAt prof p K₀) (hF : HasDerivAt (fun k => F k L₀) F1 K₀) : p = F1 := by
  have hmin : IsLocalMin (fun K => prof K - (F K L₀ - w * L₀)) K₀ := by
    filter_upwards [hle] with K hK
    simp only [heq, sub_self]
    linarith
  have d : HasDerivAt (fun K => prof K - (F K L₀ - w * L₀)) (p - (F1 - 0)) K₀ :=
    hp.sub (hF.sub (hasDerivAt_const K₀ _))
  have := hmin.hasDerivAt_eq_zero d
  linarith

/-- The Cobb–Douglas production function `F(K, L) = K^{α_k} L^{α_l}` (Miao, p. 277). -/
noncomputable def iv_cd (ak al : ℝ) (K L : ℝ) : ℝ := K ^ ak * L ^ al

/-- The optimal labour input for the Cobb–Douglas firm at wage `w`:
`L*(K) = (α_l/w)^{1/(1−α_l)} K^{α_k/(1−α_l)}`, which is `(α_l K^{α_k}/w)^{1/(1−α_l)}`
(`iv_cdLabour_eq`). -/
noncomputable def iv_cdLabour (ak al w K : ℝ) : ℝ :=
  (al / w) ^ (1 / (1 - al)) * K ^ (ak / (1 - al))

/-- The coefficient `A = (α_l/w)^{α_l/(1−α_l)} (1 − α_l)` of the Cobb–Douglas operating profit
(Miao, p. 277). -/
noncomputable def iv_cdA (al w : ℝ) : ℝ := (al / w) ^ (al / (1 - al)) * (1 - al)

/-- Miao, p. 277: `L*(K) = (α_l K^{α_k}/w)^{1/(1−α_l)}`, the solution of the first-order
condition `α_l K^{α_k} L^{α_l − 1} = w`. -/
theorem iv_cdLabour_eq {ak al w K : ℝ} (hal : al < 1) (hal0 : 0 < al) (hw : 0 < w)
    (hK : 0 < K) :
    iv_cdLabour ak al w K = (al * K ^ ak / w) ^ (1 / (1 - al)) := by
  unfold iv_cdLabour
  have h1 : 0 < 1 - al := by linarith
  rw [mul_div_right_comm, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hK.le]
  congr 2
  field_simp

/-- Miao, p. 277: the first-order condition for labour holds at `L*(K)`:
`α_l K^{α_k} L*^{α_l − 1} = w`. -/
theorem iv_cd_foc {ak al w K : ℝ} (hal : al < 1) (hal0 : 0 < al) (hw : 0 < w) (hK : 0 < K) :
    al * K ^ ak * iv_cdLabour ak al w K ^ (al - 1) = w := by
  unfold iv_cdLabour
  have h1 : 0 < 1 - al := by linarith
  have hc : 0 < al / w := by positivity
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc.le,
    ← Real.rpow_mul hK.le]
  have e1 : 1 / (1 - al) * (al - 1) = -1 := by field_simp; ring
  have e2 : ak / (1 - al) * (al - 1) = -ak := by field_simp; ring
  rw [e1, e2, Real.rpow_neg_one, Real.rpow_neg hK.le]
  field_simp

/-- Miao, p. 277: `L*(K)` maximises `F(K, L) − wL` over `L ≥ 0` (Cobb–Douglas, `0 < α_l < 1`).
Proof by Bernoulli's inequality `(1 + s)^{α_l} ≤ 1 + α_l s`. -/
theorem iv_cd_max {ak al w K : ℝ} (hal : al < 1) (hal0 : 0 < al) (hw : 0 < w) (hK : 0 < K)
    {L : ℝ} (hL : 0 ≤ L) :
    iv_cd ak al K L - w * L ≤
      iv_cd ak al K (iv_cdLabour ak al w K) - w * iv_cdLabour ak al w K := by
  set Ls := iv_cdLabour ak al w K with hLs
  have hLs0 : 0 < Ls := by unfold Ls iv_cdLabour; positivity
  have hfoc := iv_cd_foc (ak := ak) hal hal0 hw hK
  rw [← hLs] at hfoc
  have hb := rpow_one_add_le_one_add_mul_self (s := L / Ls - 1)
    (by have : 0 ≤ L / Ls := by positivity
        linarith) hal0.le hal.le
  rw [add_sub_cancel, Real.div_rpow hL hLs0.le] at hb
  have hLa : 0 < Ls ^ al := Real.rpow_pos_of_pos hLs0 al
  rw [div_le_iff₀ hLa] at hb
  have hsub : Ls ^ (al - 1) = Ls ^ al / Ls := Real.rpow_sub_one hLs0.ne' al
  rw [hsub] at hfoc
  have hKa : 0 < K ^ ak := Real.rpow_pos_of_pos hK ak
  unfold iv_cd
  have key : K ^ ak * L ^ al ≤ K ^ ak * Ls ^ al + al * K ^ ak * (Ls ^ al / Ls) * (L - Ls) := by
    have : K ^ ak * L ^ al ≤ K ^ ak * ((1 + al * (L / Ls - 1)) * Ls ^ al) :=
      mul_le_mul_of_nonneg_left hb hKa.le
    calc K ^ ak * L ^ al ≤ K ^ ak * ((1 + al * (L / Ls - 1)) * Ls ^ al) := this
      _ = K ^ ak * Ls ^ al + al * K ^ ak * (Ls ^ al / Ls) * (L - Ls) := by
        field_simp
  rw [hfoc] at key
  linarith

/-- Miao, p. 277: the Cobb–Douglas operating profit
`π(K) = max_L K^{α_k}L^{α_l} − wL = K^{α_k/(1−α_l)} (α_l/w)^{α_l/(1−α_l)} (1 − α_l)`,
i.e. `π(K) = A K^{α_k/(1−α_l)}`. -/
theorem iv_cd_profit {ak al w K : ℝ} (hal : al < 1) (hw : 0 < w) (hal0 : 0 < al) (hK : 0 < K) :
    iv_cd ak al K (iv_cdLabour ak al w K) - w * iv_cdLabour ak al w K =
      iv_cdA al w * K ^ (ak / (1 - al)) := by
  unfold iv_cd iv_cdLabour iv_cdA
  have h1 : 0 < 1 - al := by linarith
  have hc : 0 < al / w := by positivity
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hc.le,
    ← Real.rpow_mul hK.le]
  have e1 : 1 / (1 - al) * al = al / (1 - al) := by field_simp
  have hK2 : K ^ ak * K ^ (ak / (1 - al) * al) = K ^ (ak / (1 - al)) := by
    rw [← Real.rpow_add hK]
    congr 1
    field_simp
    ring
  have hc2 : (al / w) ^ (1 / (1 - al)) = (al / w) ^ (al / (1 - al)) * (al / w) := by
    rw [← Real.rpow_add_one hc.ne']
    congr 1
    field_simp
    ring
  rw [e1, hc2]
  have : K ^ ak * ((al / w) ^ (al / (1 - al)) * K ^ (ak / (1 - al) * al)) =
      (al / w) ^ (al / (1 - al)) * (K ^ ak * K ^ (ak / (1 - al) * al)) := by ring
  rw [this, hK2]
  field_simp

/-- Miao, p. 277: the envelope condition for the Cobb–Douglas firm,
`π′(K) = F₁(K, L*(K)) = α_k K^{α_k − 1} L*(K)^{α_l}`, where `π(K) = A K^{α_k/(1−α_l)}`
(`iv_cd_profit`). Proved by the envelope argument `iv_envelope_profit`, as in the book. -/
theorem iv_cd_envelope {ak al w K : ℝ} (hal : al < 1) (hw : 0 < w) (hal0 : 0 < al)
    (hK : 0 < K) :
    HasDerivAt (fun x => iv_cdA al w * x ^ (ak / (1 - al)))
      (ak * K ^ (ak - 1) * iv_cdLabour ak al w K ^ al) K := by
  set L₀ := iv_cdLabour ak al w K
  have hL0 : 0 < L₀ := by unfold L₀ iv_cdLabour; positivity
  have hp : HasDerivAt (fun x => iv_cdA al w * x ^ (ak / (1 - al)))
      (iv_cdA al w * (ak / (1 - al) * K ^ (ak / (1 - al) - 1))) K :=
    (Real.hasDerivAt_rpow_const (Or.inl hK.ne')).const_mul _
  have hF : HasDerivAt (fun k => iv_cd ak al k L₀) (ak * K ^ (ak - 1) * L₀ ^ al) K :=
    (Real.hasDerivAt_rpow_const (Or.inl hK.ne')).mul_const _
  have hle : ∀ᶠ k in 𝓝 K, iv_cd ak al k L₀ - w * L₀ ≤ iv_cdA al w * k ^ (ak / (1 - al)) := by
    filter_upwards [Ioi_mem_nhds hK] with k hk
    rw [← iv_cd_profit hal hw hal0 hk]
    exact iv_cd_max hal hal0 hw hk hL0.le
  have heq : iv_cdA al w * K ^ (ak / (1 - al)) = iv_cd ak al K L₀ - w * L₀ :=
    (iv_cd_profit hal hw hal0 hK).symm
  have := iv_envelope_profit hle heq hp hF
  rw [← this]
  exact hp

/-- Miao, p. 277: under constant returns `α_k + α_l = 1`, `π(K) = AK`. -/
theorem iv_cd_crs {ak al w K : ℝ} (hal : al < 1) (hw : 0 < w) (hal0 : 0 < al) (hK : 0 < K)
    (hcrs : ak + al = 1) :
    iv_cd ak al K (iv_cdLabour ak al w K) - w * iv_cdLabour ak al w K = iv_cdA al w * K := by
  rw [iv_cd_profit hal hw hal0 hK]
  have h1 : 0 < 1 - al := by linarith
  have : ak / (1 - al) = 1 := by rw [div_eq_one_iff_eq h1.ne']; linarith
  rw [this, Real.rpow_one]

/-- Miao, p. 277: under increasing returns `α_k + α_l > 1`, `π(K) = A K^{α_k/(1−α_l)}` is
(strictly) convex on `K ≥ 0`. -/
theorem iv_cd_convex {ak al w : ℝ} (hal : al < 1) (hw : 0 < w) (hal0 : 0 < al)
    (hirs : 1 < ak + al) :
    StrictConvexOn ℝ (Set.Ici 0) (fun K => iv_cdA al w * K ^ (ak / (1 - al))) := by
  have h1 : 0 < 1 - al := by linarith
  have hθ : 1 < ak / (1 - al) := by rw [lt_div_iff₀ h1]; linarith
  have hA : 0 < iv_cdA al w := by unfold iv_cdA; positivity
  have hs := strictConvexOn_rpow hθ
  refine ⟨hs.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have := hs.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at this ⊢
  nlinarith [mul_lt_mul_of_pos_left this hA]

/-- Miao, p. 277: under decreasing returns `α_k + α_l < 1`, `π(K) = A K^{α_k/(1−α_l)}` is
(strictly) concave on `K ≥ 0` (here `α_k > 0`). -/
theorem iv_cd_concave {ak al w : ℝ} (hal : al < 1) (hw : 0 < w) (hal0 : 0 < al) (hak : 0 < ak)
    (hdrs : ak + al < 1) :
    StrictConcaveOn ℝ (Set.Ici 0) (fun K => iv_cdA al w * K ^ (ak / (1 - al))) := by
  have h1 : 0 < 1 - al := by linarith
  have hθ : ak / (1 - al) < 1 := by rw [div_lt_one h1]; linarith
  have hθ0 : 0 < ak / (1 - al) := by positivity
  have hA : 0 < iv_cdA al w := by unfold iv_cdA; positivity
  have hs := Real.strictConcaveOn_rpow hθ0 hθ
  refine ⟨hs.1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  have := hs.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at this ⊢
  nlinarith [mul_lt_mul_of_pos_left this hA]

end Miao.Applications
